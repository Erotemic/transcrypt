use super::listings::{parse_diff_tree, tree_record};
use super::objects::close_objects;
use super::*;
use transcrypt_v3_core::is_object_id;

/// Repetitions of a test of a race-dependent outcome.
const RACE_ROUNDS: usize = 20;
/// Rounds of randomized parser mutation.
const FUZZ_ROUNDS: usize = 20_000;
/// Marsaglia's xorshift64 (shifts 13, 7, 17) from a fixed seed.
const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
const SHIFTS: (u32, u32, u32) = (13, 7, 17);
/// The most mutations applied to one fuzz input.
const MAX_MUTATIONS: u64 = 3;
/// The exit status of the test's early-exiting subprocess.
const EARLY_EXIT: i32 = 3;
/// Bound on a test that must not hang on an endless producer.
const HANG_LIMIT: std::time::Duration = std::time::Duration::from_secs(20);

/// A subprocess that exits without reading its input is an error, not
/// a silent death by SIGPIPE (which `main` does not ignore).
#[test]
fn early_exit_of_a_subprocess_is_reported() {
    crate::os::default_sigpipe();
    // Larger than any pipe buffer, so the writer is still writing.
    const BEYOND_PIPE_BUFFER: usize = 4 * MIB;
    let input = vec![b'x'; BEYOND_PIPE_BUFFER];
    for _ in 0..RACE_ROUNDS {
        let mut command = Command::new("sh");
        command.args(["-c", &format!("exit {EARLY_EXIT}")]);
        match run_bounded_status(command, Some(&input), SHORT_OUTPUT_LIMIT) {
            Ok(finished) => assert_eq!(finished.status.code(), Some(EARLY_EXIT)),
            Err(e) => assert!(e.contains("cannot send input"), "{e}"),
        }
    }
}

/// Reads of objects follow the repository they name: one thread may read
/// from several (each with its own `cat-file`), never one through
/// another's.
#[test]
fn object_reads_follow_their_repository() {
    let base = std::env::temp_dir().join(format!("transcrypt-v3-two-repos-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let repos: Vec<(PathBuf, &[u8])> = [("a", b"in a".as_slice()), ("b", b"in b")].into_iter()
        .map(|(name, bytes)| (base.join(name), bytes)).collect();
    let mut oids = Vec::new();
    for (root, bytes) in &repos {
        std::fs::create_dir_all(root).unwrap();
        git(root, &["init", "-q"]).unwrap();
        oids.push(hash_object(root, bytes).unwrap());
    }
    for _ in 0..2 {
        for ((root, bytes), oid) in repos.iter().zip(&oids) {
            assert_eq!(git_blob(root, oid).unwrap(), *bytes);
        }
    }
    close_objects();
    std::fs::remove_dir_all(&base).unwrap();
}

/// `IndexUpdate` stages exactly the given bytes at exactly the given
/// paths, whatever they contain (fast-import commands, newlines, NULs).
#[test]
fn index_updates_stage_exact_blobs() {
    let root = std::env::temp_dir().join(format!("transcrypt-v3-index-update-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    git(&root, &["init", "-q"]).unwrap();
    let blobs: [(&[u8], &[u8]); 4] = [
        (b"empty", b""),
        (b"commands", b"done\nget-mark :1\nblob\nmark :9\ndata 3\n"),
        // A newline is a file name character on Unix only.
        (if cfg!(unix) { b"dir/binary\n name" } else { b"dir/binary name" }, b"\0\xff\n\n"),
        (b"no newline", b"x"),
    ];
    for kind in [Blobs::Records, Blobs::Plaintext] {
        git(&root, &["read-tree", "--empty"]).unwrap();
        let mut update = IndexUpdate::new(&root, kind);
        for (path, bytes) in blobs { update.add(REGULAR_FILE_MODE, path, bytes).unwrap(); }
        update.apply(&["--add"]).unwrap();
        let listing = git(&root, &["ls-files", "--stage", "-z"]).unwrap();
        assert_eq!(listing.split(|b| *b == 0).filter(|r| !r.is_empty()).count(), blobs.len());
        for (path, bytes) in blobs {
            let oid = git_with_input(&root, &["hash-object", "--stdin"], bytes).unwrap();
            let oid = String::from_utf8(oid).unwrap();
            let mut record = format!("100644 {} 0\t", oid.trim_end()).into_bytes();
            record.extend_from_slice(path);
            assert!(listing.split(|b| *b == 0).any(|r| r == &record[..]), "{}", String::from_utf8_lossy(path));
            assert_eq!(git(&root, &["cat-file", "blob", oid.trim_end()]).unwrap(), bytes);
        }
    }
    // More marks than a pipe buffer holds answers for: the import's
    // output is drained while the requests are still being written.
    const MANY: usize = 4096;
    git(&root, &["read-tree", "--empty"]).unwrap();
    let mut update = IndexUpdate::new(&root, Blobs::Records);
    for i in 0..MANY { update.add(REGULAR_FILE_MODE, format!("many/{i}").as_bytes(), i.to_string().as_bytes()).unwrap(); }
    update.apply(&["--add"]).unwrap();
    assert_eq!(records(&git(&root, &["ls-files", "--stage", "-z"]).unwrap()).count(), MANY);
    // A path Git refuses to stage (it only warns, and succeeds) is an error.
    let mut update = IndexUpdate::new(&root, Blobs::Records);
    update.add(REGULAR_FILE_MODE, b".git/hooks/pre-commit", b"x").unwrap();
    let err = update.apply(&["--add"]).unwrap_err();
    assert!(err.contains("did not stage .git/hooks/pre-commit"), "{err}");
    std::fs::remove_dir_all(&root).unwrap();
}

/// `is_record`, which reads only a blob's size and first bytes, decides
/// as the keyless check of the whole blob does, and leaves the shared
/// `cat-file --batch` stream in step for the reads after it.
#[test]
fn header_only_record_checks_agree_with_whole_blobs() {
    use transcrypt_v3_core::{encode_file_header, record_envelope_ok, FILE_HEADER_LEN, FILE_MIN_LEN, ID_LEN};
    let root = std::env::temp_dir().join(format!("transcrypt-v3-is-record-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    git(&root, &["init", "-q"]).unwrap();
    let id = [7u8; ID_LEN];
    let mut other = id;
    other[0] ^= 1;
    let record = |size: usize| {
        let mut bytes = encode_file_header(&id).to_vec();
        bytes.resize(size, b'\n');
        bytes
    };
    let blobs = [
        Vec::new(),
        b"plaintext".to_vec(),
        record(FILE_HEADER_LEN),
        record(FILE_MIN_LEN - 1),
        record(FILE_MIN_LEN),
        record(FILE_MIN_LEN + 1),
        record(MAX_RECORD),
        record(MAX_RECORD + 1),
        vec![b'\n'; MAX_RECORD],
    ];
    let oids: Vec<String> = blobs.iter().map(|bytes| hash_object(&root, bytes).unwrap()).collect();
    for (bytes, oid) in blobs.iter().zip(&oids) {
        for want in [&id, &other] {
            assert_eq!(is_record(&root, oid, want).unwrap(), record_envelope_ok(bytes, want), "{} bytes", bytes.len());
        }
        // The next full read on the same stream gets exactly its blob.
        if bytes.len() <= MAX_RECORD {
            assert_eq!(&git_blob(&root, oid).unwrap(), bytes);
        }
    }
    assert!(is_record(&root, &oids[4], &id).unwrap() && is_record(&root, &oids[6], &id).unwrap());
    close_objects();
    std::fs::remove_dir_all(&root).unwrap();
}

/// Randomized robustness of the adapter's parsers of Git output: no
/// input panics, every accepted record round-trips to exactly what Git
/// would print for it, and mutations of valid input are either rejected
/// or still exact.
#[test]
fn git_output_parsers_never_panic_and_accept_only_exact_records() {
    let oid = "0123456789abcdef0123456789abcdef01234567";
    let mut state = SEED;
    let mut next = move || { state ^= state << SHIFTS.0; state ^= state >> SHIFTS.1; state ^= state << SHIFTS.2; state };
    let alphabet = b"0123456789abcdef :\t\n\0blobtreeAMDT.secret/-";
    let valid_tree = format!("100644 blob {oid}\tdir/a b.secret").into_bytes();
    let valid_diff = format!(":100644 100644 {oid} {oid} M\0dir/a\tb.secret\0").into_bytes();
    let bases: [&[u8]; 3] = [&valid_tree, &valid_diff, b""];
    for round in 0..FUZZ_ROUNDS {
        let mut input = bases[round % bases.len()].to_vec();
        for _ in 0..(next() % (MAX_MUTATIONS + 1)) {
            let at = (next() as usize) % (input.len() + 1);
            let byte = alphabet[(next() as usize) % alphabet.len()];
            // Insert, replace or remove one byte.
            const MUTATION_KINDS: u64 = 3;
            match next() % MUTATION_KINDS {
                0 => input.insert(at, byte),
                1 if at < input.len() => input[at] = byte,
                _ if at < input.len() => { input.remove(at); },
                _ => {},
            }
        }
        if let Ok(record) = tree_record(&input) {
            if let Ok(parsed) = Listing::parse([record.as_slice(), b"\0"].concat()) {
                for e in parsed.into_entries() {
                    assert!(is_object_id(e.oid.as_bytes()));
                    assert!(input.ends_with(&e.path) && input.starts_with(&input[..MODE_LEN]));
                }
            }
        }
        if let Ok(Changes { entries, .. }) = parse_diff_tree(&input) {
            for e in entries {
                assert!(is_object_id(e.oid.as_bytes()));
                let mut needle = e.path.clone();
                needle.push(0);
                assert!(input.windows(needle.len()).any(|w| w == needle.as_slice()), "{:?}", String::from_utf8_lossy(&input));
            }
        }
        let header = [oid.as_bytes(), b" blob ", input.as_slice()].concat();
        if let Some(size) = parse_batch_header(&header, oid.as_bytes()) {
            assert_eq!(header, format!("{oid} blob {size}\n").as_bytes());
        }
    }
    // The valid records parse to exactly their fields.
    let tree = Listing::parse([tree_record(&valid_tree).unwrap().as_slice(), b"\0"].concat()).unwrap().into_entries();
    assert_eq!((tree[0].regular, tree[0].oid.as_str(), tree[0].path.as_slice()), (true, oid, &b"dir/a b.secret"[..]));
    let diff = parse_diff_tree(&valid_diff).unwrap().entries;
    assert_eq!((diff[0].regular, diff[0].oid.as_str(), diff[0].path.as_slice()), (true, oid, &b"dir/a\tb.secret"[..]));
    assert_eq!(parse_batch_header(format!("{oid} blob 12\n").as_bytes(), oid.as_bytes()), Some(12));
    for bad in ["blob 12\n", " blob 012\n", " blob +12\n", " blob 12", " tree 12\n", " missing\n"] {
        let header = if bad.starts_with(' ') { format!("{oid}{bad}") } else { bad.to_owned() };
        assert_eq!(parse_batch_header(header.as_bytes(), oid.as_bytes()), None, "{bad:?}");
    }
    let changes = parse_diff_tree(format!(":100644 100644 {oid} {oid} D\0gone.secret\0").as_bytes()).unwrap();
    assert!(changes.entries.is_empty()
        && changes.deleted == [PathBlob { path: b"gone.secret".to_vec(), oid: oid.to_owned() }]);
}

#[test]
fn subprocess_output_is_bounded_and_the_producer_killed() {
    // An endless producer: refused at the limit instead of buffered, and
    // killed rather than waited for forever.
    let mut command = Command::new("sh");
    command.args(["-c", "yes transcrypt; echo noise >&2"]);
    let started = std::time::Instant::now();
    let err = run_bounded(command, None, SHORT_OUTPUT_LIMIT).unwrap_err();
    assert!(err.contains("exceeds"), "{err}");
    assert!(started.elapsed() < HANG_LIMIT);
    // Endless error output is drained, never blocking the child.
    let mut command = Command::new("sh");
    // Far more error output than is kept, or than a pipe buffers.
    const ERROR_FLOOD: usize = 5_000_000;
    command.args(["-c", &format!("head -c {ERROR_FLOOD} /dev/zero >&2; echo done")]);
    assert_eq!(run_bounded(command, None, SHORT_OUTPUT_LIMIT).unwrap(), b"done\n");
}
