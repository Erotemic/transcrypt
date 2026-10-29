//! Git subprocesses: bounded execution, object reads by verified id, and
//! index, tree and diff listings parsed by the verified core.

use std::{
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
use zeroize::Zeroizing;
pub(crate) use crate::os::sigpipe_blocked;
pub(crate) use crate::listing::{paths_of, Listing, OrderedListing, Staged};
use transcrypt_v3_core::{
    blob_read, is_object_id, parse_attr_response, parse_batch_header, parse_index_entry, record_envelope_prefix_ok,
    BlobRead, ATTRIBUTES_NAME, ATTRIBUTES_SUFFIX, ENVELOPE_PREFIX_LEN, FILTER_DRIVER, MAX_FILE, MAX_RECORD, REGULAR_MODE,
};
use transcrypt_rs::{states_mib_limit, KIB, MIB};

/// The Git mode of a non-executable regular file (the core's `REGULAR_MODE`).
pub(crate) const REGULAR_FILE_MODE: &str = match std::str::from_utf8(&REGULAR_MODE) {
    Ok(mode) => mode,
    Err(_) => panic!("REGULAR_MODE is ASCII"),
};
/// The Git mode of a submodule (a gitlink).
pub(crate) const GITLINK_MODE: &str = "160000";

/// Bytes in the mode field that starts every index record.
pub(crate) const MODE_LEN: usize = REGULAR_MODE.len();
/// Where the object id starts in an index record: after the mode and a SP.
pub(crate) const OID_START: usize = MODE_LEN + 1;
/// The stage-0 field between an index record's object id and its path.
const STAGE_ZERO_FIELD: &[u8] = b" 0\t";
/// An unmerged index record's ` <stage>` field, just before its TAB.
const STAGE_FIELD_LEN: usize = 2;
/// The stages of an unmerged index entry: base, ours and theirs.
const CONFLICT_STAGES: std::ops::RangeInclusive<u8> = b'1'..=b'3';
/// `git check-attr -z` prints each answer as path, attribute and value.
const CHECK_ATTR_FIELDS: usize = 3;

/// The output limit for a Git command that prints only a short answer or
/// nothing (its errors are kept separately).
pub(crate) const SHORT_OUTPUT_LIMIT: usize = MIB;
/// How much of a subprocess's error output is kept for its error message.
const KEPT_ERROR_OUTPUT: usize = 64 * KIB;
/// The chunk size in which subprocess output is read.
const READ_CHUNK: usize = 64 * KIB;
/// The longest `git cat-file --batch` header line read: well beyond any
/// valid one (a SHA-256 id, ` blob `, a 20-digit size and LF).
const BATCH_HEADER_LIMIT: u64 = 160;
/// How much a wiped buffer at least grows when it is full.
const GROWTH_FACTOR: usize = 2;

/// The repository's public v3 configuration, relative to the worktree root.
pub(crate) const CONFIG_PATH: &str = ".transcrypt/config";

/// The value in `slot`, computed by `init` (and kept) if there is none yet.
pub(crate) fn get_or_try_init<T, E>(slot: &mut Option<T>, init: impl FnOnce() -> Result<T, E>) -> Result<&mut T, E> {
    let value = match slot.take() { Some(value) => value, None => init()? };
    Ok(slot.insert(value))
}

/// The most any Git subprocess may print to us. Listings of a hostile index
/// or tree beyond this are refused (and the process killed), not buffered.
const GIT_OUTPUT_LIMIT: usize = 256 * MIB;

fn output(command: Command) -> Result<Vec<u8>, String> {
    run_bounded(command, None, GIT_OUTPUT_LIMIT)
}

/// Run a subprocess with `input` (if any) fed from another thread, at most
/// `limit` bytes of output accepted (beyond that it is killed), and at most
/// 64 KiB of its error output kept (the rest is drained so it never blocks).
fn run_bounded(command: Command, input: Option<&[u8]>, limit: usize) -> Result<Vec<u8>, String> {
    let desc = format!("{:?}", command);
    let Finished { status, mut output, errors } = run_bounded_status(command, input, limit)?;
    if !status.success() {
        return Err(format!("Git command failed ({desc}): {}", String::from_utf8_lossy(&errors)));
    }
    Ok(std::mem::take(&mut *output))
}

/// A finished subprocess.
pub(crate) struct Finished {
    pub(crate) status: std::process::ExitStatus,
    /// Its output, wiped when dropped (it may be plaintext).
    pub(crate) output: Zeroizing<Vec<u8>>,
    /// The kept part of its error output.
    pub(crate) errors: Vec<u8>,
}

/// `run_bounded`, returning the exit status (and output, which may be
/// plaintext, kept in wiped memory) instead of failing on a non-zero exit.
pub(crate) fn run_bounded_status(mut command: Command, input: Option<&[u8]>, limit: usize)
    -> Result<Finished, String>
{
    let desc = format!("{:?}", command);
    command.stdin(if input.is_some() { Stdio::piped() } else { Stdio::null() })
        .stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|e| format!("cannot run {desc}: {e}"))?;
    let stdin = child.stdin.take();
    let mut stderr = child.stderr.take().ok_or("subprocess error pipe missing")?;
    let mut stdout = child.stdout.take().ok_or("subprocess output pipe missing")?;
    std::thread::scope(|scope| {
        let writer = input.zip(stdin).map(|(bytes, mut stdin)| scope.spawn(move || sigpipe_blocked(&mut stdin, |stdin| stdin.write_all(bytes))));
        let errors = scope.spawn(move || {
            let mut kept = Vec::new();
            let _ = (&mut stderr).take(KEPT_ERROR_OUTPUT as u64).read_to_end(&mut kept);
            let _ = io::copy(&mut stderr, &mut io::sink());
            kept
        });
        let data = read_wiped(&mut stdout, limit);
        // Close our end first: a producer (or its children) still writing then
        // gets EPIPE instead of blocking with the error pipe open.
        drop(stdout);
        if data.is_err() { let _ = child.kill(); }
        let status = child.wait().map_err(|_| format!("cannot wait for {desc}"))?;
        let written = writer.map(|w| w.join().map_err(|_| ()).and_then(|r| r.map_err(|_| ())));
        let errors = errors.join().unwrap_or_default();
        let data = data.map_err(|_| format!("output of {desc} exceeds the {} MiB limit", limit / MIB))?;
        if matches!(written, Some(Err(()))) {
            return Err(format!("cannot send input to {desc}: {}", String::from_utf8_lossy(&errors)));
        }
        Ok(Finished { status, output: data, errors })
    })
}

/// Why `read_wiped` stopped.
pub(crate) enum ReadError {
    Failed,
    TooLarge,
}

/// Read at most `limit` bytes into memory that is wiped when dropped,
/// including every smaller buffer it outgrows.
pub(crate) fn read_wiped(read: &mut impl Read, limit: usize) -> Result<Zeroizing<Vec<u8>>, ReadError> {
    let mut out = Zeroizing::new(Vec::new());
    let mut chunk = Zeroizing::new([0u8; READ_CHUNK]);
    loop {
        let n = read.read(&mut chunk[..]).map_err(|_| ReadError::Failed)?;
        if n == 0 { return Ok(out); }
        if out.len() + n > limit { return Err(ReadError::TooLarge); }
        append_wiped(&mut out, &chunk[..n]);
    }
}

/// Append without leaving an unwiped copy behind when the buffer grows.
pub(crate) fn append_wiped(buffer: &mut Zeroizing<Vec<u8>>, data: &[u8]) {
    if buffer.len() + data.len() > buffer.capacity() {
        let mut bigger = Zeroizing::new(Vec::with_capacity((buffer.len() + data.len()).max(GROWTH_FACTOR * buffer.capacity())));
        bigger.extend_from_slice(buffer);
        *buffer = bigger;
    }
    buffer.extend_from_slice(data);
}

/// Every Git subprocess. Pathspecs are literal, so a tracked file named
/// `[a].secret` or `:(glob)*` can never select other files, and replace
/// refs are ignored, so an object id names exactly the bytes hashed into it.
pub(crate) fn git_command(root: Option<&Path>) -> Command {
    let mut command = Command::new("git");
    if let Some(root) = root { command.current_dir(root); }
    command.env("GIT_LITERAL_PATHSPECS", "1").env("GIT_NO_REPLACE_OBJECTS", "1");
    command
}

pub(crate) fn git(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = git_command(Some(root));
    command.args(arguments);
    output(command)
}

/// `rev-parse -q --verify` exits with this status, printing nothing, exactly
/// when the name resolves to no object of the requested type.
const NO_SUCH_REVISION: i32 = 1;

/// The commit `rev` names: `None` if it names none (an unborn branch, an
/// absent pseudo-ref); an error if Git fails in any other way, never a
/// silent `None`.
pub(crate) fn resolve_commit(root: &Path, rev: &str) -> Result<Option<String>, String> {
    let mut command = git_command(Some(root));
    command.args(["rev-parse", "-q", "--verify", &format!("{rev}^{{commit}}")]);
    let Finished { status, output, errors } = run_bounded_status(command, None, GIT_OUTPUT_LIMIT)?;
    match status.code() {
        Some(0) => {
            let id = String::from_utf8_lossy(&output).trim_end().to_owned();
            if !is_object_id(id.as_bytes()) { return Err("malformed git rev-parse output".into()); }
            Ok(Some(id))
        },
        Some(NO_SUCH_REVISION) if errors.is_empty() => Ok(None),
        _ => Err(format!("cannot resolve {rev}: {}", String::from_utf8_lossy(&errors).trim())),
    }
}

pub(crate) fn git_with_input(root: &Path, arguments: &[&str], input: &[u8]) -> Result<Vec<u8>, String> {
    let mut command = git_command(Some(root));
    command.args(arguments);
    run_bounded(command, Some(input), GIT_OUTPUT_LIMIT)
}

/// This worktree's Git directory and the one shared by all worktrees of the
/// repository (the same directory for an ordinary checkout).
struct GitDirs {
    git_dir: PathBuf,
    common_dir: PathBuf,
}

static GIT_DIRS: std::sync::OnceLock<GitDirs> = std::sync::OnceLock::new();

/// This worktree's own Git directory (`.git`, or `.git/worktrees/<name>`
/// for a linked worktree): private staging and scratch files go here.
/// `repo_root` records both directories for every command run in a
/// worktree; the `root/.git` fallback serves only code run without it (unit
/// tests; the bare-repository `audit` finds its own).
pub(crate) fn git_dir(root: &Path) -> PathBuf {
    GIT_DIRS.get().map_or_else(|| root.join(".git"), |d| d.git_dir.clone())
}

/// The Git directory shared by all worktrees: hooks, `info/`, and the key
/// agent, so one `unlock` serves every worktree.
pub(crate) fn common_dir(root: &Path) -> PathBuf {
    GIT_DIRS.get().map_or_else(|| root.join(".git"), |d| d.common_dir.clone())
}

/// The worktree root, after recording its Git directories.
pub(crate) fn repo_root() -> Result<PathBuf, String> {
    let mut command = git_command(None);
    command.args(["rev-parse", "--path-format=absolute", "--show-toplevel", "--git-dir", "--git-common-dir"]);
    let bytes = output(command)?;
    let text = String::from_utf8(bytes).map_err(|_| "repository path is not UTF-8")?;
    let [root, git_dir, common_dir] = text.lines().collect::<Vec<_>>()[..] else {
        return Err("not inside a Git worktree".into());
    };
    let (root, git_dir, common_dir) = (PathBuf::from(root), PathBuf::from(git_dir), PathBuf::from(common_dir));
    if !root.is_dir() || !git_dir.is_dir() || !common_dir.is_dir() {
        return Err("Git repository directories are missing".into());
    }
    let _ = GIT_DIRS.set(GitDirs { git_dir, common_dir });
    Ok(root)
}

/// The refusal of anything larger than a v3 record.
pub(crate) const TOO_LARGE: &str = "input exceeds the 16 MiB v3 size limit";
const _: () = assert!(states_mib_limit(TOO_LARGE, MAX_FILE));

/// Read at most a v3 record's worth of bytes, into wiped memory.
pub(crate) fn read_record(mut read: impl Read) -> Result<Zeroizing<Vec<u8>>, String> {
    read_wiped(&mut read, MAX_RECORD).map_err(|e| match e {
        ReadError::Failed => "cannot read input".into(),
        ReadError::TooLarge => TOO_LARGE.into(),
    })
}

/// The content of one Git blob, named by an id the verified core accepted
/// (never revision syntax such as `:path`, which reads `:0:x.secret` as stage
/// 0 of `x.secret`). Reads stop at the v3 size bound, so a hostile oversized
/// blob is refused without being loaded. All reads of one process share a
/// single `git cat-file --batch`.
pub(crate) fn git_blob(root: &Path, oid: &str) -> Result<Vec<u8>, String> {
    read_blob(root, oid, false)?.ok_or_else(|| TOO_LARGE.into())
}

/// Like `git_blob`, but `None` for a blob larger than any v3 record (an
/// ordinary large file, which cannot be a record), skipped unread.
pub(crate) fn git_blob_if_record_sized(root: &Path, oid: &str) -> Result<Option<Vec<u8>>, String> {
    read_blob(root, oid, true)
}

/// Whether blob `oid` has the v3 record envelope of the config `id`. Only
/// its size and first `ENVELOPE_PREFIX_LEN` bytes are read, which decide the
/// envelope exactly as the whole blob would (`record_envelope_prefix_ok`);
/// the rest is skipped unread.
pub(crate) fn is_record(root: &Path, oid: &str, id: &[u8; transcrypt_v3_core::ID_LEN]) -> Result<bool, String> {
    let prefix = with_objects(root, oid, |objects| objects.blob_prefix(oid))?;
    Ok(prefix.is_some_and(|(size, prefix)| record_envelope_prefix_ok(size, &prefix, id)))
}

fn read_blob(root: &Path, oid: &str, skip_large: bool) -> Result<Option<Vec<u8>>, String> {
    with_objects(root, oid, |objects| objects.blob(oid, skip_large))
}

/// Run `read` on this thread's object reader for the verified id `oid`.
fn with_objects<T>(root: &Path, oid: &str, read: impl FnOnce(&mut Objects) -> Result<T, String>) -> Result<T, String> {
    if !is_object_id(oid.as_bytes()) {
        return Err("invalid Git object id".into());
    }
    OBJECTS.with(|cell| {
        let mut slot = cell.borrow_mut();
        let result = get_or_try_init(&mut slot, || Objects::open(root)).and_then(read);
        if result.is_err() {
            // The stream may be out of step; never reuse it.
            *slot = None;
        }
        result
    })
}

thread_local! {
    static OBJECTS: std::cell::RefCell<Option<Objects>> = const { std::cell::RefCell::new(None) };
}

/// A `git cat-file --batch` reply that ended early.
const TRUNCATED_REPLY: &str = "truncated git cat-file reply";
/// A `git cat-file --batch` reply whose content is not followed by LF.
const MALFORMED_REPLY: &str = "malformed git cat-file reply";

/// One `git cat-file --batch` process. Each reply must be exactly
/// `<oid> blob <size> LF`, with `<size>` in canonical decimal, followed by
/// `<size>` bytes and LF; anything else (a missing object, another type, a
/// different id, a malformed or oversized header) is an error, so bytes can
/// never be attributed to the wrong object.
struct Objects {
    child: std::process::Child,
    input: Option<std::process::ChildStdin>,
    output: io::BufReader<std::process::ChildStdout>,
}

impl Objects {
    fn open(root: &Path) -> Result<Objects, String> {
        let mut child = git_command(Some(root))
            .args(["cat-file", "--batch"])
            .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null())
            .spawn().map_err(|e| format!("cannot run git cat-file: {e}"))?;
        let input = child.stdin.take().ok_or("git cat-file input pipe missing")?;
        let output = child.stdout.take().ok_or("git cat-file output pipe missing")?;
        Ok(Objects { child, input: Some(input), output: io::BufReader::new(output) })
    }

    /// Ask for `oid` and read the header of the reply, which the verified
    /// core checks: the blob's size.
    fn request(&mut self, oid: &str) -> Result<u64, String> {
        use io::BufRead;
        let input = self.input.as_mut().ok_or("Git object reader closed")?;
        sigpipe_blocked(input, |input| input.write_all(format!("{oid}\n").as_bytes()).and_then(|_| input.flush()))
            .map_err(|_| "cannot query git cat-file")?;
        let mut header = Vec::new();
        (&mut self.output).take(BATCH_HEADER_LIMIT).read_until(b'\n', &mut header)
            .map_err(|_| "cannot read git cat-file reply")?;
        parse_batch_header(&header, oid.as_bytes()).ok_or_else(|| format!("Git object {oid} is missing or not a blob"))
    }

    /// Discard the next `count` content bytes without keeping them, then
    /// the reply's trailing LF.
    fn skip(&mut self, count: u64) -> Result<(), String> {
        let skipped = io::copy(&mut (&mut self.output).take(count), &mut io::sink()).map_err(|_| TRUNCATED_REPLY)?;
        if skipped != count {
            return Err(TRUNCATED_REPLY.into());
        }
        let mut end = [0u8; 1];
        self.output.read_exact(&mut end).map_err(|_| TRUNCATED_REPLY)?;
        if end != *b"\n" {
            return Err(MALFORMED_REPLY.into());
        }
        Ok(())
    }

    fn blob(&mut self, oid: &str, skip_large: bool) -> Result<Option<Vec<u8>>, String> {
        // The verified core checks the header and decides what to read.
        let size = self.request(oid)?;
        match blob_read(size, skip_large) {
            BlobRead::Read => {},
            BlobRead::TooLarge => return Err(TOO_LARGE.into()),
            BlobRead::Skip => {
                self.skip(size)?;
                return Ok(None);
            },
        }
        // `blob_read` decided `Read`, so `size` is at most `MAX_RECORD`.
        let size = usize::try_from(size).map_err(|_| TOO_LARGE)?;
        let mut data = vec![0u8; size + 1];
        self.output.read_exact(&mut data).map_err(|_| TRUNCATED_REPLY)?;
        if data.pop() != Some(b'\n') {
            return Err(MALFORMED_REPLY.into());
        }
        Ok(Some(data))
    }

    /// The size of blob `oid` and its first `ENVELOPE_PREFIX_LEN` bytes (all
    /// of a shorter blob): what the keyless envelope check needs. The rest is
    /// skipped unread, and so is a blob larger than any record (`None`).
    fn blob_prefix(&mut self, oid: &str) -> Result<Option<(usize, Vec<u8>)>, String> {
        let announced = self.request(oid)?;
        match blob_read(announced, true) {
            BlobRead::Read => {},
            BlobRead::TooLarge => return Err(TOO_LARGE.into()),
            BlobRead::Skip => {
                self.skip(announced)?;
                return Ok(None);
            },
        }
        // `blob_read` decided `Read`, so the size is at most `MAX_RECORD`.
        let size = usize::try_from(announced).map_err(|_| TOO_LARGE)?;
        let mut prefix = vec![0u8; size.min(ENVELOPE_PREFIX_LEN)];
        self.output.read_exact(&mut prefix).map_err(|_| TRUNCATED_REPLY)?;
        self.skip(announced - prefix.len() as u64)?;
        Ok(Some((size, prefix)))
    }
}

impl Drop for Objects {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Whether `path` is a `.gitattributes` file (at the top or nested).
pub(crate) fn is_attributes_file(path: &[u8]) -> bool {
    path == ATTRIBUTES_NAME || path.ends_with(&ATTRIBUTES_SUFFIX)
}

/// The non-empty NUL-separated records of Git `-z` output.
pub(crate) fn records(data: &[u8]) -> impl Iterator<Item = &[u8]> {
    data.split(|b| *b == 0).filter(|record| !record.is_empty())
}

/// `records` of a listing that must end with its last record's NUL.
fn complete_records(data: &[u8]) -> Result<impl Iterator<Item = &[u8]>, String> {
    if !data.is_empty() && data.last() != Some(&0) {
        return Err("truncated Git listing".into());
    }
    Ok(records(data))
}

/// The exact index listing (`ls-files --stage -z`), unmerged stages included.
pub(crate) fn index_listing(root: &Path) -> Result<Vec<u8>, String> {
    git(root, &["ls-files", "--stage", "-z"])
}

/// One `<mode> SP <oid> SP 0 TAB <path>` record (see `Listing`).
fn parse_entry(entry: &[u8]) -> Result<Staged, String> {
    let parsed = parse_index_entry(entry)
        .map_err(|_| "malformed or unmerged Git index entry; resolve conflicts first")?;
    let oid = &entry[OID_START..parsed.path_start - STAGE_ZERO_FIELD.len()];
    if !is_object_id(oid) {
        return Err("malformed Git object id in index entry".into());
    }
    Staged::new(parsed.regular, &entry[..MODE_LEN], oid, &entry[parsed.path_start..])
}

/// The blobs of a commit's tree.
pub(crate) fn tree_files(root: &Path, commit: &str) -> Result<Vec<Staged>, String> {
    Ok(tree_listing(root, commit)?.into_entries())
}

/// `tree_files`, as a `Listing`.
pub(crate) fn tree_listing(root: &Path, commit: &str) -> Result<Listing, String> {
    Listing::parse(tree_listing_bytes(root, &["ls-tree", "-r", "-z", "--full-tree", commit])?)
}

/// An `ls-tree -z` listing rewritten to index records. `ls-tree` prints
/// `<mode> SP <type> SP <oid> TAB <path>` (every Git version; `--format`
/// needs 2.36); each record is rewritten as `<mode> SP <oid> SP 0 TAB
/// <path>`, with the path copied verbatim, so that the verified core parses
/// and checks the listing exactly like an index listing.
fn tree_listing_bytes(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    for entry in records(&git(root, arguments)?) {
        bytes.extend_from_slice(&tree_record(entry)?);
        bytes.push(0);
    }
    Ok(bytes)
}

/// Rewrite one `ls-tree` record as `<mode> SP <oid> SP 0 TAB <path>`.
fn tree_record(entry: &[u8]) -> Result<Vec<u8>, String> {
    let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed git ls-tree record")?;
    let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
    let [mode, _kind, oid] = fields[..] else { return Err("malformed git ls-tree record".into()) };
    Ok([mode, b" ", oid, STAGE_ZERO_FIELD, &entry[tab + 1..]].concat())
}

/// The index during a merge: its exact listing, the stage-0 entries (parsed
/// by the verified core) and, once each, the paths of unmerged entries
/// (`<mode> SP <oid> SP <1|2|3> TAB <path>`; Git lists stages of a path
/// together).
pub(crate) struct Index {
    pub(crate) listing: Vec<u8>,
    pub(crate) merged: Vec<Staged>,
    pub(crate) conflicted: Vec<Vec<u8>>,
}

pub(crate) fn index_with_conflicts(root: &Path) -> Result<Index, String> {
    let listing = index_listing(root)?;
    let mut merged = Vec::new();
    let mut conflicted: Vec<Vec<u8>> = Vec::new();
    for entry in complete_records(&listing)? {
        let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed Git index entry")?;
        if tab >= STAGE_FIELD_LEN && entry[tab - STAGE_FIELD_LEN] == b' ' && CONFLICT_STAGES.contains(&entry[tab - 1]) {
            let path = entry[tab + 1..].to_vec();
            if conflicted.last() != Some(&path) { conflicted.push(path); }
        } else {
            merged.push(parse_entry(entry)?);
        }
    }
    Ok(Index { merged, listing, conflicted })
}

/// The stage-0 entries of the index (`Listing::parse`).
pub(crate) fn indexed_files(root: &Path) -> Result<Vec<Staged>, String> {
    Ok(Listing::parse(index_listing(root)?)?.into_entries())
}

/// The blobs Git already has for exactly `path`: every index stage, and
/// `HEAD`'s. Used to let a filter pass bytes through unchanged only when
/// they are one of these, never because of a header alone. A path that is
/// not UTF-8 (which cannot be passed as an argument on every OS) has none:
/// fail-closed, since the filter then never passes bytes through for it.
pub(crate) fn blobs_at(root: &Path, path: &[u8]) -> Result<Vec<String>, String> {
    let name = std::str::from_utf8(path).ok().map(str::to_owned);
    let mut oids = Vec::new();
    let mut parse = |listing: &[u8], tree: bool| {
        for entry in records(listing) {
            let Some(tab) = entry.iter().position(|b| *b == b'\t') else { continue };
            if &entry[tab + 1..] != path { continue; }
            let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
            // `<mode> <oid> <stage>` (index) or `<mode> <type> <oid>` (tree).
            const INDEX_OID_FIELD: usize = 1;
            const TREE_OID_FIELD: usize = 2;
            let oid = fields.get(if tree { TREE_OID_FIELD } else { INDEX_OID_FIELD });
            if let Some(oid) = oid.filter(|o| is_object_id(o)) {
                oids.push(String::from_utf8_lossy(oid).into_owned());
            }
        }
    };
    let Some(name) = name else { return Ok(oids) };
    parse(&git(root, &["ls-files", "--stage", "-z", "--", &name])?, false);
    if let Ok(listing) = git(root, &["ls-tree", "-z", "HEAD", "--", &name]) { parse(&listing, true); }
    Ok(oids)
}

/// The object id Git gives `bytes` (nothing is written).
pub(crate) fn blob_id(root: &Path, bytes: &[u8]) -> Result<String, String> {
    object_id(git_with_input(root, &["hash-object", "--no-filters", "--stdin"], bytes)?)
}

/// Write `bytes` as a Git blob, unfiltered; its verified object id.
pub(crate) fn hash_object(root: &Path, bytes: &[u8]) -> Result<String, String> {
    object_id(git_with_input(root, &["hash-object", "-w", "--no-filters", "--stdin"], bytes)?)
}

/// Blobs to stage at paths: written by one `git fast-import` (from stdin, so
/// no content touches a temporary file), then staged by one `update-index -z
/// --index-info`. One process each, however many files.
#[derive(Default)]
pub(crate) struct IndexUpdate {
    stream: Zeroizing<Vec<u8>>,
    entries: Vec<(String, Vec<u8>)>,
}

impl IndexUpdate {
    /// Stage `bytes` (unfiltered) as a blob of `mode` at `path`.
    pub(crate) fn add(&mut self, mode: &str, path: &[u8], bytes: &[u8]) {
        self.entries.push((mode.to_owned(), path.to_owned()));
        append_wiped(&mut self.stream, format!("blob\nmark :{}\ndata {}\n", self.entries.len(), bytes.len()).as_bytes());
        append_wiped(&mut self.stream, bytes);
        append_wiped(&mut self.stream, b"\n");
    }

    pub(crate) fn len(&self) -> usize { self.entries.len() }

    /// Write the blobs and stage them, with `update-index` `options` (such as
    /// `--add`). `--done` makes a truncated stream fail without writing.
    /// `update-index` skips a path it considers invalid (on Windows, one that
    /// NTFS cannot name) with only a warning and success, so the index is
    /// read back: every entry must now be staged exactly.
    pub(crate) fn apply(mut self, root: &Path, options: &[&str]) -> Result<(), String> {
        if self.entries.is_empty() { return Ok(()); }
        for mark in 1..=self.entries.len() {
            append_wiped(&mut self.stream, format!("get-mark :{mark}\n").as_bytes());
        }
        append_wiped(&mut self.stream, b"done\n");
        let oids = git_with_input(root, &["fast-import", "--quiet", "--done"], &self.stream)?;
        let oids: Vec<&[u8]> = oids.split(|b| *b == b'\n').filter(|l| !l.is_empty()).collect();
        if oids.len() != self.entries.len() || !oids.iter().all(|oid| is_object_id(oid)) {
            return Err("malformed git fast-import output".into());
        }
        let mut info = Vec::new();
        for ((mode, path), oid) in self.entries.iter().zip(&oids) {
            push_index_record(&mut info, mode, &String::from_utf8_lossy(oid), path);
        }
        let arguments: Vec<&str> = ["update-index", "-z"].into_iter().chain(options.iter().copied())
            .chain(["--index-info"]).collect();
        git_with_input(root, &arguments, &info)?;
        let listing = index_listing(root)?;
        let staged: std::collections::HashSet<&[u8]> = records(&listing).collect();
        for ((mode, path), oid) in self.entries.iter().zip(oids) {
            let mut record = format!("{mode} {} 0\t", String::from_utf8_lossy(oid)).into_bytes();
            record.extend_from_slice(path);
            if !staged.contains(&record[..]) {
                return Err(format!("Git did not stage {} (it refuses that path name here)", String::from_utf8_lossy(path)));
            }
        }
        Ok(())
    }
}

/// Append the `update-index -z --index-info` record `<mode> SP <oid> TAB
/// <path> NUL` to `info`.
pub(crate) fn push_index_record(info: &mut Vec<u8>, mode: &str, oid: &str, path: &[u8]) {
    info.extend_from_slice(format!("{mode} {oid}\t").as_bytes());
    info.extend_from_slice(path);
    info.push(0);
}

fn object_id(output: Vec<u8>) -> Result<String, String> {
    let oid = String::from_utf8_lossy(&output).trim_end().to_owned();
    if !is_object_id(oid.as_bytes()) { return Err("malformed git hash-object output".into()); }
    Ok(oid)
}

/// Which attribute files Git consults to decide what is protected.
#[derive(Clone, Copy)]
pub(crate) enum Attributes<'a> {
    /// The staged `.gitattributes` files: what the next commit will say.
    Staged,
    /// The worktree's: what `git add` applies to a new file.
    Worktree,
    /// Those of a temporary index file (a commit's, for `audit`).
    Index(&'a Path),
}

/// `git check-attr -z --stdin <attributes>` for `paths`, sent as raw bytes
/// (any valid Unix name works), from the attribute files `from` selects.
/// Patterns match case-sensitively (`core.ignorecase=false`) so that every
/// clone, on every file system, selects the same files.
fn check_attr(root: &Path, paths: &[&[u8]], from: Attributes, attributes: &[&str]) -> Result<AttrAnswer, String> {
    if paths.iter().any(|path| path.is_empty() || path.contains(&0)) {
        return Err("invalid Git path".into());
    }
    let request = nul_terminated(paths);
    let mut command = git_command(Some(root));
    command.args(["-c", "core.ignorecase=false", "check-attr"]);
    match from {
        Attributes::Staged => { command.arg("--cached"); },
        Attributes::Worktree => {},
        Attributes::Index(file) => { command.arg("--cached").env("GIT_INDEX_FILE", file); },
    }
    command.args(["-z", "--stdin"]).args(attributes);
    let response = run_bounded(command, Some(&request), GIT_OUTPUT_LIMIT)?;
    Ok(AttrAnswer { request, response })
}

/// What `check_attr` sent Git (`nul_terminated` paths) and Git's answer.
struct AttrAnswer {
    request: Vec<u8>,
    response: Vec<u8>,
}

/// Each path joined into one buffer, each followed by NUL.
pub(crate) fn nul_terminated<P: AsRef<[u8]>>(paths: &[P]) -> Vec<u8> {
    paths.iter().flat_map(|path| path.as_ref().iter().copied().chain([0])).collect()
}

/// For each path, whether Git's effective `filter` attribute is
/// `transcrypt-v3`. Git evaluates its own attribute rules (patterns, nested
/// files, macros, `.git/info/attributes`); the whole answer is parsed by the
/// verified core (`parse_attr_response_spec`), which requires one record per
/// requested path, in order, and nothing else.
pub(crate) fn protected_flags(root: &Path, paths: &[&[u8]], from: Attributes) -> Result<Vec<bool>, String> {
    if paths.is_empty() { return Ok(Vec::new()); }
    let answer = check_attr(root, paths, from, &["filter"])?;
    let mut flags = vec![false; paths.len()];
    if !parse_attr_response(&answer.request, &answer.response, &mut flags) {
        return Err("unexpected git check-attr output".into());
    }
    Ok(flags)
}

/// For each entry of `listing`, whether Git's effective `filter` attribute
/// is `transcrypt-v3`. Git's answer is parsed by the verified core against
/// the listing's own paths (`parse_listing_attrs_spec`): one record per
/// entry, in order, naming exactly that entry's path, and nothing else.
pub(crate) fn listing_flags(root: &Path, listing: &Listing, from: Attributes) -> Result<Vec<bool>, String> {
    if listing.entries().is_empty() { return Ok(Vec::new()); }
    let answer = check_attr(root, &paths_of(listing.entries()), from, &["filter"])?;
    listing.attribute_flags(&answer.response).ok_or_else(|| "unexpected git check-attr output".into())
}

/// For each path, its value of each of `attributes` (`unspecified`, `unset`,
/// `set` or a value), for checks that only ever refuse: an answer that does
/// not name exactly the requested paths and attributes, in order, is an error.
pub(crate) fn attr_values(root: &Path, paths: &[&[u8]], from: Attributes, attributes: &[&str])
    -> Result<Vec<Vec<Vec<u8>>>, String>
{
    if paths.is_empty() { return Ok(Vec::new()); }
    let response = check_attr(root, paths, from, attributes)?.response;
    let fields: Vec<&[u8]> = response.split(|b| *b == 0).collect();
    let width = CHECK_ATTR_FIELDS * attributes.len();
    if fields.len() != width * paths.len() + 1 || fields.last() != Some(&&b""[..]) {
        return Err("unexpected git check-attr output".into());
    }
    paths.iter().zip(fields.chunks(width)).map(|(path, record)| {
        record.chunks(CHECK_ATTR_FIELDS).zip(attributes).map(|(field, name)| match field {
            [p, n, value] if p == path && *n == name.as_bytes() => Ok(value.to_vec()),
            _ => Err("unexpected git check-attr output".into()),
        }).collect()
    }).collect()
}

/// Each path's `filter` attribute value.
pub(crate) fn filter_values(root: &Path, paths: &[&[u8]], from: Attributes) -> Result<Vec<Vec<u8>>, String> {
    Ok(attr_values(root, paths, from, &["filter"])?.into_iter().flatten().collect())
}

/// Whether a `filter` value hands the file to another named filter driver
/// (not unset or unspecified, which are deliberate exclusions).
pub(crate) fn other_filter(value: &[u8]) -> bool {
    value != FILTER_DRIVER && !matches!(value, b"unspecified" | b"unset")
}

/// Whether Git resolves the `transcrypt` macro to `filter=transcrypt-v3`
/// for a commit whose top-level `.gitattributes` is the blob `top`: probed
/// in a temporary index (in `index_dir`) holding that file and a directory
/// whose own rules say `probe transcrypt`. Local attribute files apply, as
/// they do to Git's filters. A missing, redefined or overridden macro all
/// show as a probe Git would not encrypt. The hooks and the audit use this
/// one predicate.
pub(crate) fn macro_resolves(root: &Path, index_dir: &Path, top: Option<&str>) -> Result<bool, String> {
    let rules = hash_object(root, b"probe transcrypt\n")?;
    let mut info = Vec::new();
    push_index_record(&mut info, REGULAR_FILE_MODE, &rules, b"transcrypt-v3-probe/.gitattributes");
    if let Some(top) = top { push_index_record(&mut info, REGULAR_FILE_MODE, top, &ATTRIBUTES_NAME); }
    let index = index_dir.join(format!("transcrypt-v3-probe-{}.index", std::process::id()));
    let _ = std::fs::remove_file(&index);
    let mut command = git_command(Some(root));
    command.env("GIT_INDEX_FILE", &index).args(["update-index", "-z", "--index-info"]);
    let result = run_bounded(command, Some(&info), SHORT_OUTPUT_LIMIT)
        .and_then(|_| protected_flags(root, &[b"transcrypt-v3-probe/probe"], Attributes::Index(&index)));
    let _ = std::fs::remove_file(&index);
    Ok(result?.first() == Some(&true))
}

/// A path marked `transcrypt` whose `filter` is neither `transcrypt-v3` nor
/// explicitly unset: the macro is broken for it, whatever any probe says
/// (a rule can target the probe's own path). `None` when there is none.
pub(crate) fn marked_unfiltered(root: &Path, paths: &[&[u8]], from: Attributes) -> Result<Option<String>, String> {
    let values = attr_values(root, paths, from, &["transcrypt", "filter"])?;
    for (path, values) in paths.iter().zip(&values) {
        let [mark, filter] = &values[..] else { return Err("unexpected git check-attr output".into()) };
        if mark == b"set" && *filter != FILTER_DRIVER && filter != b"unset" {
            let name = String::from_utf8_lossy(path);
            return Ok(Some(if filter == b"unspecified" {
                format!("{name}: {}", crate::attributes::MACRO_MISSING)
            } else {
                format!("{name} is marked `transcrypt`, but another rule gives it the filter `{}` (from \
                    `git lfs track`?), so it would be stored unencrypted; narrow that rule",
                    String::from_utf8_lossy(filter))
            }));
        }
    }
    Ok(None)
}

/// The entries among `entries` that Git's attributes protect.
pub(crate) fn protected_entries(root: &Path, entries: Vec<Staged>, from: Attributes) -> Result<Vec<Staged>, String> {
    let flags = protected_flags(root, &paths_of(&entries), from)?;
    Ok(entries.into_iter().zip(flags).filter(|(_, protected)| *protected).map(|(e, _)| e).collect())
}

/// A path and the blob it holds (or held).
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct PathBlob {
    pub(crate) path: Vec<u8>,
    pub(crate) oid: String,
}

/// What a commit changes relative to its parent.
pub(crate) struct Changes {
    /// The entries it adds or changes, as they are in the commit.
    pub(crate) entries: Vec<Staged>,
    /// The paths it deletes, with their old blobs.
    pub(crate) deleted: Vec<PathBlob>,
    /// The paths it modifies, with their old blobs.
    pub(crate) modified: Vec<PathBlob>,
}

/// The entries a commit adds or changes relative to `parent` (all of its
/// entries for a root commit), from `diff-tree -r -z --raw` between the two
/// trees, rewritten to the index-record shape and parsed by the verified
/// core, and the paths it deletes with their old object ids.
pub(crate) fn changed_files(root: &Path, commit: &str, parent: Option<&str>) -> Result<Changes, String> {
    let Some(parent) = parent else {
        return Ok(Changes { entries: tree_files(root, commit)?, deleted: Vec::new(), modified: Vec::new() });
    };
    let data = git(root, &["diff-tree", "-r", "-z", "--raw", "--no-renames", "--no-abbrev", parent, commit])?;
    parse_diff_tree(&data)
}

/// Parse `diff-tree -r -z --raw` records,
/// `:<old mode> <new mode> <old oid> <new oid> <status> NUL <path> NUL`, keeping
/// the new side of every entry that is not deleted, and the deleted paths
/// with their old object ids.
fn parse_diff_tree(data: &[u8]) -> Result<Changes, String> {
    if !data.is_empty() && data.last() != Some(&0) {
        return Err("truncated git diff-tree output".into());
    }
    let mut fields = data.split(|b| *b == 0);
    let mut entries = Vec::new();
    let mut deleted = Vec::new();
    let mut modified = Vec::new();
    while let Some(header) = fields.next() {
        if header.is_empty() { break; }
        let path = fields.next().ok_or("malformed git diff-tree output")?;
        let parts: Vec<&[u8]> = header.strip_prefix(b":").ok_or("malformed git diff-tree output")?
            .split(|b| *b == b' ').collect();
        let [_, mode, old, oid, status] = parts[..] else { return Err("malformed git diff-tree output".into()) };
        let old = || -> Result<_, String> {
            if !is_object_id(old) { return Err("malformed git diff-tree output".into()); }
            Ok(PathBlob { path: path.to_vec(), oid: String::from_utf8_lossy(old).into_owned() })
        };
        match status {
            b"D" => { deleted.push(old()?); continue },
            b"A" => {},
            b"M" | b"T" => modified.push(old()?),
            _ => return Err("unexpected git diff-tree status".into()),
        }
        entries.push(parse_entry(&[mode, b" ", oid, b" 0\t", path].concat())?);
    }
    Ok(Changes { entries, deleted, modified })
}

/// The `.transcrypt/config` blob of a commit, if it has one.
pub(crate) fn config_blob(root: &Path, commit: &str) -> Result<Option<String>, String> {
    let listing = tree_listing_bytes(root, &["ls-tree", "-z", "--full-tree", commit, "--", CONFIG_PATH])?;
    Ok(Listing::parse(listing)?.into_entries().into_iter()
        .find(|e| e.path == CONFIG_PATH.as_bytes() && e.regular).map(|e| e.oid))
}

/// Re-index exactly `paths`, whose worktree content cleans to the staged
/// blob, and check that no staged blob or mode changed from `listing`.
pub(crate) fn reindex(root: &Path, listing: &[u8], paths: &[Vec<u8>]) -> Result<(), String> {
    if paths.is_empty() { return Ok(()); }
    git_with_input(root, &["update-index", "-z", "--stdin"], &nul_terminated(paths))?;
    if index_listing(root)? != listing {
        return Err("staged Git objects changed while refreshing the index; inspect `git diff --cached`".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
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
        let mut update = IndexUpdate::default();
        for (path, bytes) in blobs { update.add(REGULAR_FILE_MODE, path, bytes); }
        update.apply(&root, &["--add"]).unwrap();
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
        // A path Git refuses to stage (it only warns, and succeeds) is an error.
        let mut update = IndexUpdate::default();
        update.add(REGULAR_FILE_MODE, b".git/hooks/pre-commit", b"x");
        let err = update.apply(&root, &["--add"]).unwrap_err();
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
}
