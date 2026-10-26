//! Git subprocesses: bounded execution, object reads by verified id, and
//! index, tree and diff listings parsed by the verified core.

use std::{
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
use std::os::unix::ffi::OsStrExt;
use zeroize::Zeroizing;
use transcrypt_v3_core::{
    blob_read, is_object_id, listing_fields, parse_attr_response, parse_batch_header, parse_index_entry,
    parse_listing as parse_listing_ends, parse_listing_attrs, BlobRead, MAX_RECORD,
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
fn run_bounded(command: Command, input: Option<&[u8]>, limit: usize) -> Result<Vec<u8>, String> {
    let desc = format!("{:?}", command);
    let (status, mut data, errors) = run_bounded_status(command, input, limit)?;
    if !status.success() {
        return Err(format!("Git command failed ({desc}): {}", String::from_utf8_lossy(&errors)));
    }
    Ok(std::mem::take(&mut *data))
}

/// A finished subprocess: exit status, output (wiped when dropped) and the
/// kept part of its error output.
pub(crate) type Finished = (std::process::ExitStatus, Zeroizing<Vec<u8>>, Vec<u8>);

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
        let writer = input.zip(stdin).map(|(bytes, mut stdin)| scope.spawn(move || sigpipe_blocked(|| stdin.write_all(bytes))));
        let errors = scope.spawn(move || {
            let mut kept = Vec::new();
            let _ = (&mut stderr).take(64 * 1024).read_to_end(&mut kept);
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
        let data = data.map_err(|_| format!("output of {desc} exceeds the {} MiB limit", limit >> 20))?;
        if matches!(written, Some(Err(()))) {
            return Err(format!("cannot send input to {desc}: {}", String::from_utf8_lossy(&errors)));
        }
        Ok((status, data, errors))
    })
}

/// Run `f` with SIGPIPE blocked in this thread, so that a write to a pipe
/// or socket whose reader is gone fails with EPIPE (an error that is
/// reported, and rolled back from) instead of killing the process: `main`
/// restores SIGPIPE's default so that `transcrypt-v3 status | head` ends
/// quietly.
pub(crate) fn sigpipe_blocked<T>(f: impl FnOnce() -> T) -> T {
    // SAFETY: signal-mask calls on initialized sets; `sigwait` returns at
    // once because the signal it waits for is pending.
    unsafe {
        let mut pipe: libc::sigset_t = std::mem::zeroed();
        libc::sigemptyset(&mut pipe);
        libc::sigaddset(&mut pipe, libc::SIGPIPE);
        let mut previous: libc::sigset_t = std::mem::zeroed();
        libc::pthread_sigmask(libc::SIG_BLOCK, &pipe, &mut previous);
        let result = f();
        // Discard a SIGPIPE raised meanwhile, then restore the mask.
        let mut pending: libc::sigset_t = std::mem::zeroed();
        if libc::sigpending(&mut pending) == 0 && libc::sigismember(&pending, libc::SIGPIPE) == 1 {
            let mut signal = 0;
            libc::sigwait(&pipe, &mut signal);
        }
        libc::pthread_sigmask(libc::SIG_SETMASK, &previous, std::ptr::null_mut());
        result
    }
}

/// Read at most `limit` bytes into memory that is wiped when dropped,
/// including every smaller buffer it outgrows.
pub(crate) fn read_wiped(read: &mut impl Read, limit: usize) -> Result<Zeroizing<Vec<u8>>, String> {
    let mut out = Zeroizing::new(Vec::new());
    let mut chunk = Zeroizing::new([0u8; 64 * 1024]);
    loop {
        let n = read.read(&mut chunk[..]).map_err(|_| "cannot read input")?;
        if n == 0 { return Ok(out); }
        if out.len() + n > limit { return Err("input exceeds its size limit".into()); }
        append_wiped(&mut out, &chunk[..n]);
    }
}

/// Append without leaving an unwiped copy behind when the buffer grows.
pub(crate) fn append_wiped(buffer: &mut Zeroizing<Vec<u8>>, data: &[u8]) {
    if buffer.len() + data.len() > buffer.capacity() {
        let mut bigger = Zeroizing::new(Vec::with_capacity((buffer.len() + data.len()).max(2 * buffer.capacity())));
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

/// Read at most a v3 record's worth of bytes, into wiped memory.
pub(crate) fn read_record(mut read: impl Read) -> Result<Zeroizing<Vec<u8>>, String> {
    read_wiped(&mut read, MAX_RECORD).map_err(|e| if e == "cannot read input" { e } else { TOO_LARGE.into() })
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

/// Whether blob `oid` has the v3 record envelope of the config `id` (a blob
/// too large for any record has not, and is skipped unread).
pub(crate) fn is_record(root: &Path, oid: &str, id: &[u8; transcrypt_v3_core::ID_LEN]) -> Result<bool, String> {
    Ok(git_blob_if_record_sized(root, oid)?.is_some_and(|blob| transcrypt_v3_core::record_envelope_ok(&blob, id)))
}

fn read_blob(root: &Path, oid: &str, skip_large: bool) -> Result<Option<Vec<u8>>, String> {
    if !is_object_id(oid.as_bytes()) {
        return Err("invalid Git object id".into());
    }
    OBJECTS.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.is_none() {
            *slot = Some(Objects::open(root)?);
        }
        let objects = slot.as_mut().ok_or("Git object reader unavailable")?;
        let result = objects.blob(oid, skip_large);
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

    fn blob(&mut self, oid: &str, skip_large: bool) -> Result<Option<Vec<u8>>, String> {
        use io::BufRead;
        let input = self.input.as_mut().ok_or("Git object reader closed")?;
        sigpipe_blocked(|| input.write_all(format!("{oid}\n").as_bytes()).and_then(|_| input.flush()))
            .map_err(|_| "cannot query git cat-file")?;
        let mut header = Vec::new();
        (&mut self.output).take(160).read_until(b'\n', &mut header)
            .map_err(|_| "cannot read git cat-file reply")?;
        // The verified core checks the header and decides what to read.
        let size = parse_batch_header(&header, oid.as_bytes())
            .ok_or_else(|| format!("Git object {oid} is missing or not a blob"))?;
        match blob_read(size, skip_large) {
            BlobRead::Read => {},
            BlobRead::TooLarge => return Err(TOO_LARGE.into()),
            BlobRead::Skip => {
                // Skip the content (and its LF) without keeping it.
                let skipped = io::copy(&mut (&mut self.output).take(size.saturating_add(1)), &mut io::sink())
                    .map_err(|_| "truncated git cat-file reply")?;
                if skipped != size.saturating_add(1) {
                    return Err("truncated git cat-file reply".into());
                }
                return Ok(None);
            },
        }
        // `blob_read` decided `Read`, so `size` is at most `MAX_RECORD`.
        let size = usize::try_from(size).map_err(|_| TOO_LARGE)?;
        let mut data = vec![0u8; size + 1];
        self.output.read_exact(&mut data).map_err(|_| "truncated git cat-file reply")?;
        if data.pop() != Some(b'\n') {
            return Err("malformed git cat-file reply".into());
        }
        Ok(Some(data))
    }
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
    /// The mode is 100644 or 100755 (`mode`): a file Git filters.
    pub(crate) regular: bool,
    pub(crate) mode: String,
    pub(crate) oid: String,
    pub(crate) path: Vec<u8>,
}

impl Staged {
    /// The path, for messages.
    pub(crate) fn name(&self) -> std::borrow::Cow<'_, str> {
        String::from_utf8_lossy(&self.path)
    }
}

/// The paths of `entries`, for `protected_flags` and `attr_values`.
pub(crate) fn paths_of(entries: &[Staged]) -> Vec<&[u8]> {
    entries.iter().map(|e| e.path.as_slice()).collect()
}

/// Whether `path` is a `.gitattributes` file (at the top or nested).
pub(crate) fn is_attributes_file(path: &[u8]) -> bool {
    path == b".gitattributes" || path.ends_with(b"/.gitattributes")
}

/// One snapshot of the index or of a commit's tree: the exact listing (Git's
/// `ls-files --stage -z`, or `ls-tree -r -z` rewritten to the same records),
/// where each record ends, and its entries. The verified core checks the
/// whole listing (`parse_listing`: NUL-terminated stage-0 records with object
/// ids, nothing else) and delimits each entry's fields (`listing_fields`);
/// the pre-commit decisions are verified functions of `bytes` and `ends`.
pub(crate) struct Listing {
    pub(crate) bytes: Vec<u8>,
    pub(crate) ends: Vec<usize>,
    pub(crate) entries: Vec<Staged>,
}

impl Listing {
    pub(crate) fn parse(bytes: Vec<u8>) -> Result<Listing, String> {
        // One slot per NUL; the core refuses unless that is exactly the
        // number of records.
        let mut ends = vec![0; bytes.iter().filter(|b| **b == 0).count()];
        if !parse_listing_ends(&bytes, &mut ends) {
            return Err("malformed or unmerged Git index entry; resolve conflicts first".into());
        }
        let entries = (0..ends.len()).map(|i| {
            let f = listing_fields(&bytes, &ends, i).ok_or("malformed Git listing")?;
            Ok(Staged {
                regular: f.regular,
                mode: String::from_utf8_lossy(&bytes[f.start..f.start + 6]).into_owned(),
                oid: String::from_utf8(bytes[f.start + 7..f.oid_end].to_vec()).map_err(|_| "malformed Git object id")?,
                path: bytes[f.path_start..f.end].to_vec(),
            })
        }).collect::<Result<_, String>>()?;
        Ok(Listing { bytes, ends, entries })
    }

    /// The listing of no entries.
    pub(crate) fn empty() -> Listing {
        Listing { bytes: Vec::new(), ends: Vec::new(), entries: Vec::new() }
    }
}

/// The entries of an index listing (`Listing::parse`).
pub(crate) fn parse_listing(data: &[u8]) -> Result<Vec<Staged>, String> {
    Ok(Listing::parse(data.to_vec())?.entries)
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

/// One `<mode> SP <oid> SP 0 TAB <path>` record (see `parse_listing`).
fn parse_entry(entry: &[u8]) -> Result<Staged, String> {
    let parsed = parse_index_entry(entry)
        .map_err(|_| "malformed or unmerged Git index entry; resolve conflicts first")?;
    let oid = &entry[7..parsed.path_start - 3];
    if !is_object_id(oid) {
        return Err("malformed Git object id in index entry".into());
    }
    Ok(Staged {
        regular: parsed.regular,
        mode: String::from_utf8_lossy(&entry[..6]).into_owned(),
        oid: String::from_utf8(oid.to_vec()).map_err(|_| "malformed Git object id")?,
        path: entry[parsed.path_start..].to_vec(),
    })
}

/// The blobs of a commit's tree. `ls-tree -r -z` prints `<mode> SP <type> SP
/// <oid> TAB <path>` (every Git version; `--format` needs 2.36); each record
/// is rewritten as `<mode> SP <oid> SP 0 TAB <path>`, with the path copied
/// verbatim, and the listing is then parsed and checked by the verified core
/// exactly like an index listing.
pub(crate) fn tree_files(root: &Path, commit: &str) -> Result<Vec<Staged>, String> {
    Ok(tree_listing(root, commit)?.entries)
}

/// `tree_files`, as a `Listing`.
pub(crate) fn tree_listing(root: &Path, commit: &str) -> Result<Listing, String> {
    Listing::parse(tree_listing_bytes(root, &["ls-tree", "-r", "-z", "--full-tree", commit])?)
}

/// An `ls-tree -z` listing rewritten to index records (`tree_record`).
pub(crate) fn tree_listing_bytes(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    for entry in records(&git(root, arguments)?) {
        bytes.extend_from_slice(&tree_record(entry)?);
        bytes.push(0);
    }
    Ok(bytes)
}

fn ls_tree(root: &Path, arguments: &[&str]) -> Result<Vec<Staged>, String> {
    Ok(Listing::parse(tree_listing_bytes(root, arguments)?)?.entries)
}

/// Rewrite one `ls-tree` record as `<mode> SP <oid> SP 0 TAB <path>`.
fn tree_record(entry: &[u8]) -> Result<Vec<u8>, String> {
    let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed git ls-tree record")?;
    let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
    let [mode, _kind, oid] = fields[..] else { return Err("malformed git ls-tree record".into()) };
    Ok([mode, b" ", oid, b" 0", &entry[tab..]].concat())
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
        if tab >= 2 && entry[tab - 2] == b' ' && matches!(entry[tab - 1], b'1'..=b'3') {
            let path = entry[tab + 1..].to_vec();
            if conflicted.last() != Some(&path) { conflicted.push(path); }
        } else {
            merged.push(parse_entry(entry)?);
        }
    }
    Ok(Index { merged, listing, conflicted })
}

pub(crate) fn indexed_files(root: &Path) -> Result<Vec<Staged>, String> {
    parse_listing(&index_listing(root)?)
}

/// The blobs Git already has for exactly `path`: every index stage, and
/// `HEAD`'s. Used to let a filter pass bytes through unchanged only when
/// they are one of these, never because of a header alone.
pub(crate) fn blobs_at(root: &Path, path: &[u8]) -> Result<Vec<String>, String> {
    let name = std::ffi::OsStr::from_bytes(path).to_str().map(str::to_owned);
    let mut oids = Vec::new();
    let mut parse = |listing: &[u8], tree: bool| {
        for entry in records(listing) {
            let Some(tab) = entry.iter().position(|b| *b == b'\t') else { continue };
            if &entry[tab + 1..] != path { continue; }
            let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
            let oid = if tree { fields.get(2) } else { fields.get(1) };
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

/// Write `bytes` as a blob and append its `update-index -z --index-info`
/// record for `path` to `info`.
pub(crate) fn push_blob_record(root: &Path, info: &mut Vec<u8>, mode: &str, path: &[u8], bytes: &[u8])
    -> Result<(), String>
{
    push_index_record(info, mode, &hash_object(root, bytes)?, path);
    Ok(())
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
/// clone, on every file system, selects the same files. Returns the request
/// and Git's answer.
fn check_attr(root: &Path, paths: &[&[u8]], from: Attributes, attributes: &[&str]) -> Result<(Vec<u8>, Vec<u8>), String> {
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
    Ok((request, response))
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
    let (request, response) = check_attr(root, paths, from, &["filter"])?;
    let mut flags = vec![false; paths.len()];
    if !parse_attr_response(&request, &response, &mut flags) {
        return Err("unexpected git check-attr output".into());
    }
    Ok(flags)
}

/// For each entry of `listing`, whether Git's effective `filter` attribute
/// is `transcrypt-v3`. Git's answer is parsed by the verified core against
/// the listing's own paths (`parse_listing_attrs_spec`): one record per
/// entry, in order, naming exactly that entry's path, and nothing else.
pub(crate) fn listing_flags(root: &Path, listing: &Listing, from: Attributes) -> Result<Vec<bool>, String> {
    if listing.entries.is_empty() { return Ok(Vec::new()); }
    let (_, response) = check_attr(root, &paths_of(&listing.entries), from, &["filter"])?;
    let mut flags = vec![false; listing.entries.len()];
    if !parse_listing_attrs(&listing.bytes, &listing.ends, &response, &mut flags) {
        return Err("unexpected git check-attr output".into());
    }
    Ok(flags)
}

/// For each path, its value of each of `attributes` (`unspecified`, `unset`,
/// `set` or a value), for checks that only ever refuse: an answer that does
/// not name exactly the requested paths and attributes, in order, is an error.
pub(crate) fn attr_values(root: &Path, paths: &[&[u8]], from: Attributes, attributes: &[&str])
    -> Result<Vec<Vec<Vec<u8>>>, String>
{
    if paths.is_empty() { return Ok(Vec::new()); }
    let (_, response) = check_attr(root, paths, from, attributes)?;
    let fields: Vec<&[u8]> = response.split(|b| *b == 0).collect();
    let width = 3 * attributes.len();
    if fields.len() != width * paths.len() + 1 || fields.last() != Some(&&b""[..]) {
        return Err("unexpected git check-attr output".into());
    }
    paths.iter().zip(fields.chunks(width)).map(|(path, record)| {
        record.chunks(3).zip(attributes).map(|(field, name)| match field {
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
    !matches!(value, b"unspecified" | b"unset" | b"transcrypt-v3")
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
    push_index_record(&mut info, "100644", &rules, b"transcrypt-v3-probe/.gitattributes");
    if let Some(top) = top { push_index_record(&mut info, "100644", top, b".gitattributes"); }
    let index = index_dir.join(format!("transcrypt-v3-probe-{}.index", std::process::id()));
    let _ = std::fs::remove_file(&index);
    let mut command = git_command(Some(root));
    command.env("GIT_INDEX_FILE", &index).args(["update-index", "-z", "--index-info"]);
    let result = run_bounded(command, Some(&info), 1 << 20)
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
        if mark == b"set" && !matches!(&filter[..], b"transcrypt-v3" | b"unset") {
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

/// Paths with their old object ids: what a commit deletes, or changes.
pub(crate) type Deleted = Vec<(Vec<u8>, String)>;

/// What a commit changes: the new entries, the deleted paths and the old
/// object ids of modified paths.
pub(crate) type Changes = (Vec<Staged>, Deleted, Deleted);

/// The entries a commit adds or changes relative to `parent` (all of its
/// entries for a root commit), from `diff-tree -r -z --raw` between the two
/// trees, rewritten to the index-record shape and parsed by the verified
/// core, and the paths it deletes with their old object ids.
pub(crate) fn changed_files(root: &Path, commit: &str, parent: Option<&str>) -> Result<Changes, String> {
    let Some(parent) = parent else { return Ok((tree_files(root, commit)?, Vec::new(), Vec::new())) };
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
            Ok((path.to_vec(), String::from_utf8_lossy(old).into_owned()))
        };
        match status {
            b"D" => { deleted.push(old()?); continue },
            b"A" => {},
            b"M" | b"T" => modified.push(old()?),
            _ => return Err("unexpected git diff-tree status".into()),
        }
        entries.push(parse_entry(&[mode, b" ", oid, b" 0\t", path].concat())?);
    }
    Ok((entries, deleted, modified))
}

/// The `.transcrypt/config` blob of a commit, if it has one.
pub(crate) fn config_blob(root: &Path, commit: &str) -> Result<Option<String>, String> {
    Ok(ls_tree(root, &["ls-tree", "-z", "--full-tree", commit, "--", ".transcrypt/config"])?.into_iter()
        .find(|e| e.path == b".transcrypt/config" && e.regular).map(|e| e.oid))
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

    /// A subprocess that exits without reading its input is an error, not
    /// a silent death by SIGPIPE (which `main` does not ignore).
    #[test]
    fn early_exit_of_a_subprocess_is_reported() {
        // SAFETY: restoring a signal's default disposition is always valid.
        unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) };
        let input = vec![b'x'; 4 << 20];
        for _ in 0..20 {
            let mut command = Command::new("sh");
            command.args(["-c", "exit 3"]);
            match run_bounded_status(command, Some(&input), 1 << 20) {
                Ok((status, _, _)) => assert_eq!(status.code(), Some(3)),
                Err(e) => assert!(e.contains("cannot send input"), "{e}"),
            }
        }
    }

    /// Randomized robustness of the adapter's parsers of Git output: no
    /// input panics, every accepted record round-trips to exactly what Git
    /// would print for it, and mutations of valid input are either rejected
    /// or still exact.
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
            if let Ok((entries, _, _)) = parse_diff_tree(&input) {
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
        let tree = parse_listing(&[tree_record(&valid_tree).unwrap().as_slice(), b"\0"].concat()).unwrap();
        assert_eq!((tree[0].regular, tree[0].oid.as_str(), tree[0].path.as_slice()), (true, oid, &b"dir/a b.secret"[..]));
        let (diff, _, _) = parse_diff_tree(&valid_diff).unwrap();
        assert_eq!((diff[0].regular, diff[0].oid.as_str(), diff[0].path.as_slice()), (true, oid, &b"dir/a\tb.secret"[..]));
        assert_eq!(parse_batch_header(format!("{oid} blob 12\n").as_bytes(), oid.as_bytes()), Some(12));
        for bad in ["blob 12\n", " blob 012\n", " blob +12\n", " blob 12", " tree 12\n", " missing\n"] {
            let header = if bad.starts_with(' ') { format!("{oid}{bad}") } else { bad.to_owned() };
            assert_eq!(parse_batch_header(header.as_bytes(), oid.as_bytes()), None, "{bad:?}");
        }
        let (kept, deleted, _) = parse_diff_tree(format!(":100644 100644 {oid} {oid} D\0gone.secret\0").as_bytes()).unwrap();
        assert!(kept.is_empty() && deleted == [(b"gone.secret".to_vec(), oid.to_owned())]);
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
