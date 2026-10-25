//! Git subprocesses: bounded execution, object reads by verified id, and
//! index, tree and diff listings parsed by the verified core.

use std::{
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
use transcrypt_v3_core::{
    check_attr_response_ok, is_object_id, parse_index_entry, MAX_RECORD,
};

/// The most any Git subprocess may print to us. Listings of a hostile index
/// or tree beyond this are refused (and the process killed), not buffered.
const GIT_OUTPUT_LIMIT: usize = 256 * 1024 * 1024;

fn output(command: Command) -> Result<Vec<u8>, String> {
    run_bounded(command, None, GIT_OUTPUT_LIMIT)
}

/// Run a subprocess with `input` (if any) fed from another thread, at most
/// `limit` bytes of output accepted (beyond that it is killed), and at most
/// 64 KiB of its error output kept (the rest is drained so it never blocks).
fn run_bounded(mut command: Command, input: Option<Vec<u8>>, limit: usize) -> Result<Vec<u8>, String> {
    let desc = format!("{:?}", command);
    command.stdin(if input.is_some() { Stdio::piped() } else { Stdio::null() })
        .stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|e| format!("cannot run {desc}: {e}"))?;
    let writer = match (input, child.stdin.take()) {
        (Some(bytes), Some(mut stdin)) => Some(std::thread::spawn(move || stdin.write_all(&bytes))),
        _ => None,
    };
    let mut stderr = child.stderr.take().ok_or("subprocess error pipe missing")?;
    let errors = std::thread::spawn(move || {
        let mut kept = Vec::new();
        let _ = (&mut stderr).take(64 * 1024).read_to_end(&mut kept);
        let _ = io::copy(&mut stderr, &mut io::sink());
        kept
    });
    let stdout = child.stdout.take().ok_or("subprocess output pipe missing")?;
    let data = read_limited(stdout, limit);
    if data.is_err() { let _ = child.kill(); }
    let status = child.wait().map_err(|_| format!("cannot wait for {desc}"))?;
    let written = writer.map(|w| w.join().map_err(|_| ()).and_then(|r| r.map_err(|_| ())));
    let errors = errors.join().unwrap_or_default();
    let data = data.map_err(|_| format!("output of {desc} exceeds the {} MiB limit", limit >> 20))?;
    if !status.success() || matches!(written, Some(Err(()))) {
        return Err(format!("Git command failed ({desc}): {}", String::from_utf8_lossy(&errors)));
    }
    Ok(data)
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

pub(crate) fn git_with_input(root: &Path, arguments: &[&str], input: &[u8]) -> Result<Vec<u8>, String> {
    let mut command = git_command(Some(root));
    command.args(arguments);
    run_bounded(command, Some(input.to_vec()), GIT_OUTPUT_LIMIT)
}

pub(crate) fn repo_root() -> Result<PathBuf, String> {
    let mut command = git_command(None);
    command.args(["rev-parse", "--show-toplevel"]);
    let bytes = output(command)?;
    let root = PathBuf::from(String::from_utf8(bytes).map_err(|_| "repository path is not UTF-8")?.trim());
    if !root.is_dir() {
        return Err("Git repository root is not a directory".into());
    }
    let git_dir = root.join(".git");
    let meta = fs::symlink_metadata(&git_dir).map_err(|_| "only normal Git checkouts with a .git directory are supported")?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err("linked worktrees and symlinked .git directories are not yet supported".into());
    }
    Ok(root)
}

pub(crate) fn read_limited<R: Read>(read: R, limit: usize) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    read.take((limit as u64) + 1).read_to_end(&mut out).map_err(|_| "cannot read input")?;
    if out.len() > limit { return Err("input exceeds the 16 MiB v3 size limit".into()); }
    Ok(out)
}

/// The content of one Git blob, named by an id the verified core accepted
/// (never revision syntax such as `:path`, which reads `:0:x.secret` as stage
/// 0 of `x.secret`). Reads stop at the v3 size bound, so a hostile oversized
/// blob is refused without being loaded. All reads of one process share a
/// single `git cat-file --batch`.
pub(crate) fn git_blob(root: &Path, oid: &str) -> Result<Vec<u8>, String> {
    if !is_object_id(oid.as_bytes()) {
        return Err("invalid Git object id".into());
    }
    OBJECTS.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.is_none() {
            *slot = Some(Objects::open(root)?);
        }
        let objects = slot.as_mut().ok_or("Git object reader unavailable")?;
        let result = objects.blob(oid);
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

    fn blob(&mut self, oid: &str) -> Result<Vec<u8>, String> {
        use io::BufRead;
        let input = self.input.as_mut().ok_or("Git object reader closed")?;
        input.write_all(format!("{oid}\n").as_bytes())
            .and_then(|_| input.flush()).map_err(|_| "cannot query git cat-file")?;
        let mut header = Vec::new();
        (&mut self.output).take(160).read_until(b'\n', &mut header)
            .map_err(|_| "cannot read git cat-file reply")?;
        let size = batch_blob_size(&header, oid)
            .ok_or_else(|| format!("Git object {oid} is missing or not a blob"))?;
        if size > MAX_RECORD {
            return Err("input exceeds the 16 MiB v3 size limit".into());
        }
        let mut data = vec![0u8; size + 1];
        self.output.read_exact(&mut data).map_err(|_| "truncated git cat-file reply")?;
        if data.pop() != Some(b'\n') {
            return Err("malformed git cat-file reply".into());
        }
        Ok(data)
    }
}

/// The size in a `cat-file --batch` reply header, which must be exactly
/// `<oid> blob <size> LF` with `<size>` in canonical decimal (checked by
/// re-serializing it).
fn batch_blob_size(header: &[u8], oid: &str) -> Option<usize> {
    header.strip_prefix(oid.as_bytes())
        .and_then(|rest| rest.strip_prefix(b" blob "))
        .and_then(|rest| rest.strip_suffix(b"\n"))
        .and_then(|digits| std::str::from_utf8(digits).ok())
        .and_then(|digits| digits.parse::<usize>().ok())
        .filter(|size| header == format!("{oid} blob {size}\n").as_bytes())
}

impl Drop for Objects {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// One stage-0 record of the index or of a commit's tree. Every later read
/// of its content goes through `oid`, so a concurrent index change cannot
/// substitute other bytes for the ones that were verified.
pub(crate) struct Staged {
    pub(crate) regular: bool,
    pub(crate) oid: String,
    pub(crate) path: Vec<u8>,
}

/// Parse NUL-separated `<mode> SP <oid> SP 0 TAB <path>` records, with paths
/// as raw bytes. Each record is parsed by the verified core
/// (`parse_index_entry`): the flag says whether the mode is exactly 100644,
/// and the path is everything after the first TAB. Its specification fixes
/// the record as `mode(6) SP oid SP "0" TAB path`, so the object id is
/// `entry[7..path_start - 3]` (Lean `indexRecord_oid`), which must also pass
/// `is_object_id`.
/// Unmerged and malformed records are refused.
pub(crate) fn parse_listing(data: &[u8]) -> Result<Vec<Staged>, String> {
    if !data.is_empty() && data.last() != Some(&0) {
        return Err("truncated Git listing".into());
    }
    let mut entries = Vec::new();
    for entry in data.split(|b| *b == 0).filter(|item| !item.is_empty()) {
        let parsed = parse_index_entry(entry)
            .map_err(|_| "malformed or unmerged Git index entry; resolve conflicts first")?;
        let oid = &entry[7..parsed.path_start - 3];
        if !is_object_id(oid) {
            return Err("malformed Git object id in index entry".into());
        }
        entries.push(Staged {
            regular: parsed.regular,
            oid: String::from_utf8(oid.to_vec()).map_err(|_| "malformed Git object id")?,
            path: entry[parsed.path_start..].to_vec(),
        });
    }
    Ok(entries)
}

/// The blobs of a commit's tree. `ls-tree -r -z` prints `<mode> SP <type> SP
/// <oid> TAB <path>` (every Git version; `--format` needs 2.36); each record
/// is rewritten as `<mode> SP <oid> SP 0 TAB <path>`, with the path copied
/// verbatim, and then parsed and checked by the verified core exactly like an
/// index record.
pub(crate) fn tree_files(root: &Path, commit: &str) -> Result<Vec<Staged>, String> {
    let data = git(root, &["ls-tree", "-r", "-z", "--full-tree", commit])?;
    let mut listing = Vec::with_capacity(data.len());
    for entry in data.split(|b| *b == 0).filter(|item| !item.is_empty()) {
        listing.extend_from_slice(&tree_record(entry)?);
        listing.push(0);
    }
    parse_listing(&listing)
}

/// Rewrite one `ls-tree` record as `<mode> SP <oid> SP 0 TAB <path>`.
fn tree_record(entry: &[u8]) -> Result<Vec<u8>, String> {
    let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed git ls-tree record")?;
    let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
    let [mode, _kind, oid] = fields[..] else { return Err("malformed git ls-tree record".into()) };
    Ok([mode, b" ", oid, b" 0", &entry[tab..]].concat())
}

pub(crate) fn indexed_files(root: &Path) -> Result<Vec<Staged>, String> {
    parse_listing(&git(root, &["ls-files", "--stage", "-z"])?)
}

/// Check Git's *effective* staged filter policy, not just the contents of the
/// committed root .gitattributes file. Per-directory attributes and the
/// checkout-local .git/info/attributes take precedence over that file.
/// `--cached` evaluates staged .gitattributes, while -z/--stdin transports
/// exact path bytes, including newlines and non-UTF8 names.
pub(crate) fn verify_staged_filter_attributes(root: &Path, paths: &[&[u8]]) -> Result<(), String> {
    if paths.is_empty() { return Ok(()); }
    if paths.iter().any(|path| path.is_empty() || path.contains(&0)) {
        return Err("invalid indexed protected path".into());
    }
    let mut request = Vec::new();
    for path in paths {
        request.extend_from_slice(path);
        request.push(0);
    }
    let response = git_with_input(root, &["check-attr", "--cached", "-z", "--stdin", "filter"], &request)?;
    if !check_attr_response_ok(&request, &response) {
        return Err("protected staged path does not have the required effective transcrypt-v3 filter".into());
    }
    Ok(())
}

/// The entries a commit adds or changes relative to `parent` (all of its
/// entries for a root commit), from `diff-tree -r -z --raw` between the two
/// trees, rewritten to the index-record shape and parsed by the verified core.
pub(crate) fn changed_files(root: &Path, commit: &str, parent: Option<&str>) -> Result<Vec<Staged>, String> {
    let Some(parent) = parent else { return tree_files(root, commit) };
    let data = git(root, &["diff-tree", "-r", "-z", "--raw", "--no-renames", "--no-abbrev", parent, commit])?;
    parse_diff_tree(&data)
}

/// Parse `diff-tree -r -z --raw` records,
/// `:<old mode> <new mode> <old oid> <new oid> <status> NUL <path> NUL`, keeping
/// the new side of every entry that is not deleted.
fn parse_diff_tree(data: &[u8]) -> Result<Vec<Staged>, String> {
    if !data.is_empty() && data.last() != Some(&0) {
        return Err("truncated git diff-tree output".into());
    }
    let mut fields = data.split(|b| *b == 0);
    let mut listing = Vec::new();
    while let Some(header) = fields.next() {
        if header.is_empty() { break; }
        let path = fields.next().ok_or("malformed git diff-tree output")?;
        let parts: Vec<&[u8]> = header.strip_prefix(b":").ok_or("malformed git diff-tree output")?
            .split(|b| *b == b' ').collect();
        let [_, mode, _, oid, status] = parts[..] else { return Err("malformed git diff-tree output".into()) };
        match status {
            b"D" => continue,
            b"A" | b"M" | b"T" => {},
            _ => return Err("unexpected git diff-tree status".into()),
        }
        listing.extend_from_slice(mode);
        listing.push(b' ');
        listing.extend_from_slice(oid);
        listing.extend_from_slice(b" 0\t");
        listing.extend_from_slice(path);
        listing.push(0);
    }
    parse_listing(&listing)
}

/// The `.transcrypt/config` blob of a commit, if it has one.
pub(crate) fn config_blob(root: &Path, commit: &str) -> Result<Option<String>, String> {
    let data = git(root, &["ls-tree", "-z", "--full-tree", commit, "--", ".transcrypt/config"])?;
    let mut listing = Vec::new();
    for entry in data.split(|b| *b == 0).filter(|e| !e.is_empty()) {
        listing.extend_from_slice(&tree_record(entry)?);
        listing.push(0);
    }
    Ok(parse_listing(&listing)?.into_iter().find(|e| e.path == b".transcrypt/config" && e.regular).map(|e| e.oid))
}

/// Re-index exactly `paths`, whose worktree content cleans to the staged
/// blob, and check that no staged blob or mode changed from `listing`.
pub(crate) fn reindex(root: &Path, listing: &[u8], paths: &[Vec<u8>]) -> Result<(), String> {
    if paths.is_empty() { return Ok(()); }
    let mut input = Vec::new();
    for path in paths {
        input.extend_from_slice(path);
        input.push(0);
    }
    git_with_input(root, &["update-index", "-z", "--stdin"], &input)?;
    if git(root, &["ls-files", "--stage", "-z"])? != listing {
        return Err("staged Git objects changed while refreshing the index; inspect `git diff --cached`".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use transcrypt_v3_core::is_object_id;

    #[test]
    fn git_output_parsers_never_panic_and_accept_only_exact_records() {
        let oid = "0123456789abcdef0123456789abcdef01234567";
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || { state ^= state << 13; state ^= state >> 7; state ^= state << 17; state };
        let alphabet = b"0123456789abcdef :\t\n\0blobtreeAMDT.secret/-";
        let valid_tree = format!("100644 blob {oid}\tdir/a b.secret").into_bytes();
        let valid_diff = format!(":100644 100644 {oid} {oid} M\0dir/a\tb.secret\0").into_bytes();
        for round in 0..20000 {
            let base: &[u8] = match round % 3 { 0 => &valid_tree, 1 => &valid_diff, _ => b"" };
            let mut input = base.to_vec();
            for _ in 0..(next() % 4) {
                let at = (next() as usize) % (input.len() + 1);
                let byte = alphabet[(next() as usize) % alphabet.len()];
                match next() % 3 {
                    0 => input.insert(at, byte),
                    1 if at < input.len() => input[at] = byte,
                    _ if at < input.len() => { input.remove(at); },
                    _ => {},
                }
            }
            if let Ok(record) = tree_record(&input) {
                if let Ok(parsed) = parse_listing(&[record.as_slice(), b"\0"].concat()) {
                    for e in parsed {
                        assert!(is_object_id(e.oid.as_bytes()));
                        assert!(input.ends_with(&e.path) && input.starts_with(&input[..6]));
                    }
                }
            }
            if let Ok(entries) = parse_diff_tree(&input) {
                for e in entries {
                    assert!(is_object_id(e.oid.as_bytes()));
                    let mut needle = e.path.clone();
                    needle.push(0);
                    assert!(input.windows(needle.len()).any(|w| w == needle.as_slice()), "{:?}", String::from_utf8_lossy(&input));
                }
            }
            let header = [oid.as_bytes(), b" blob ", input.as_slice()].concat();
            if let Some(size) = batch_blob_size(&header, oid) {
                assert_eq!(header, format!("{oid} blob {size}\n").as_bytes());
            }
        }
        // The valid records parse to exactly their fields.
        let tree = parse_listing(&[tree_record(&valid_tree).unwrap().as_slice(), b"\0"].concat()).unwrap();
        assert_eq!((tree[0].regular, tree[0].oid.as_str(), tree[0].path.as_slice()), (true, oid, &b"dir/a b.secret"[..]));
        let diff = parse_diff_tree(&valid_diff).unwrap();
        assert_eq!((diff[0].regular, diff[0].oid.as_str(), diff[0].path.as_slice()), (true, oid, &b"dir/a\tb.secret"[..]));
        assert_eq!(batch_blob_size(format!("{oid} blob 12\n").as_bytes(), oid), Some(12));
        for bad in ["blob 12\n", " blob 012\n", " blob +12\n", " blob 12", " tree 12\n", " missing\n"] {
            let header = if bad.starts_with(' ') { format!("{oid}{bad}") } else { bad.to_owned() };
            assert_eq!(batch_blob_size(header.as_bytes(), oid), None, "{bad:?}");
        }
        assert!(parse_diff_tree(format!(":100644 100644 {oid} {oid} D\0gone.secret\0").as_bytes()).unwrap().is_empty());
    }

    #[test]
    fn subprocess_output_is_bounded_and_the_producer_killed() {
        // An endless producer: refused at the limit instead of buffered, and
        // killed rather than waited for forever.
        let mut command = Command::new("sh");
        command.args(["-c", "yes transcrypt; echo noise >&2"]);
        let started = std::time::Instant::now();
        let err = run_bounded(command, None, 1 << 20).unwrap_err();
        assert!(err.contains("exceeds"), "{err}");
        assert!(started.elapsed() < std::time::Duration::from_secs(20));
        // Endless error output is drained, never blocking the child.
        let mut command = Command::new("sh");
        command.args(["-c", "head -c 5000000 /dev/zero >&2; echo done"]);
        assert_eq!(run_bounded(command, None, 1 << 20).unwrap(), b"done\n");
    }
}
