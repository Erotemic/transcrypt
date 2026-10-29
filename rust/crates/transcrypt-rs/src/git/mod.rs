//! Git subprocesses: bounded execution and the repository's directories
//! here, object reads by verified id (`objects`), index, tree and diff
//! listings parsed by the verified core (`listings`), index updates
//! (`index`) and attribute queries (`checkattr`).

mod checkattr;
mod index;
mod listings;
mod objects;
#[cfg(test)]
mod tests;

pub(crate) use checkattr::*;
pub(crate) use index::*;
pub(crate) use listings::*;
pub(crate) use objects::*;

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
    BlobRead, ATTRIBUTES_NAME, ATTRIBUTES_SUFFIX, ENVELOPE_PREFIX_LEN, FILTER_DRIVER, MAX_FILE, MAX_RECORD, OID_START,
    REGULAR_MODE,
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

/// The Git directories of each worktree root `repo_root` found.
static GIT_DIRS: std::sync::Mutex<Vec<(PathBuf, GitDirs)>> = std::sync::Mutex::new(Vec::new());

/// The recorded directory `pick` chooses for `root`, or `root/.git`.
fn recorded_dir(root: &Path, pick: impl Fn(&GitDirs) -> &PathBuf) -> PathBuf {
    let dirs = GIT_DIRS.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    dirs.iter().find(|(r, _)| r == root).map_or_else(|| root.join(".git"), |(_, d)| pick(d).clone())
}

/// This worktree's own Git directory (`.git`, or `.git/worktrees/<name>`
/// for a linked worktree): private staging and scratch files go here.
/// `repo_root` records both directories for every command run in a
/// worktree; the `root/.git` fallback serves only code run without it (unit
/// tests; the bare-repository `audit` finds its own).
pub(crate) fn git_dir(root: &Path) -> PathBuf {
    recorded_dir(root, |d| &d.git_dir)
}

/// The Git directory shared by all worktrees: hooks, `info/`, and the key
/// agent, so one `unlock` serves every worktree.
pub(crate) fn common_dir(root: &Path) -> PathBuf {
    recorded_dir(root, |d| &d.common_dir)
}

/// The worktree root, after recording its Git directories.
pub(crate) fn repo_root() -> Result<PathBuf, String> {
    // One path per command: a path may itself contain a newline, so only
    // the one Git ends its answer with is taken off.
    let path = |option: &str| -> Result<PathBuf, String> {
        let mut command = git_command(None);
        command.args(["rev-parse", "--path-format=absolute", option]);
        let bytes = output(command)?;
        let path = bytes.strip_suffix(b"\n").filter(|p| !p.is_empty()).ok_or("not inside a Git worktree")?;
        Ok(PathBuf::from(crate::os::os_string(path)?))
    };
    let (root, git_dir, common_dir) = (path("--show-toplevel")?, path("--git-dir")?, path("--git-common-dir")?);
    if !root.is_dir() || !git_dir.is_dir() || !common_dir.is_dir() {
        return Err("Git repository directories are missing".into());
    }
    let mut dirs = GIT_DIRS.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    if !dirs.iter().any(|(r, _)| *r == root) { dirs.push((root.clone(), GitDirs { git_dir, common_dir })); }
    Ok(root)
}

/// One entry of `git worktree list --porcelain`.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Worktree {
    pub(crate) path: PathBuf,
    pub(crate) bare: bool,
    /// Git found its directory gone (`prunable`): nothing there to check.
    pub(crate) prunable: bool,
}

/// The worktrees of the repository at `root`. With `-z` (Git 2.36 and
/// later) every path is exact; older Git prints a path containing a
/// newline across two lines, which `parse_worktrees` refuses rather than
/// mistakes for another worktree.
pub(crate) fn worktrees(root: &Path) -> Result<Vec<Worktree>, String> {
    match git(root, &["worktree", "list", "--porcelain", "-z"]) {
        Ok(listing) => parse_worktrees(&listing, b'\0'),
        Err(_) => parse_worktrees(&git(root, &["worktree", "list", "--porcelain"])?, b'\n'),
    }
}

/// Parse `worktree list --porcelain` whose lines end with `end` (NUL for
/// `-z`): records of `worktree <path>` and attribute lines, each record
/// ended by an empty line. Anything else, an attribute this does not know
/// included, is an error: a worktree is never silently left out.
pub(crate) fn parse_worktrees(listing: &[u8], end: u8) -> Result<Vec<Worktree>, String> {
    const MALFORMED: &str = "unexpected `git worktree list` output (a worktree path with a newline needs Git 2.36 or later)";
    if !listing.is_empty() && listing.last() != Some(&end) { return Err(MALFORMED.into()); }
    let mut worktrees = Vec::new();
    let mut current: Option<Worktree> = None;
    // The last split piece is the empty one after the final terminator.
    let mut lines = listing.split(|b| *b == end);
    lines.next_back();
    for line in lines {
        if line.is_empty() {
            worktrees.push(current.take().ok_or(MALFORMED)?);
            continue;
        }
        match (&mut current, line.strip_prefix(b"worktree ")) {
            (None, Some(path)) => {
                current = Some(Worktree { path: PathBuf::from(crate::os::os_string(path)?), bare: false, prunable: false });
            },
            (Some(worktree), None) => match line.split(|b| *b == b' ').next().unwrap_or_default() {
                b"HEAD" | b"branch" | b"detached" | b"locked" => {},
                b"bare" => worktree.bare = true,
                b"prunable" => worktree.prunable = true,
                _ => return Err(MALFORMED.into()),
            },
            _ => return Err(MALFORMED.into()),
        }
    }
    if current.is_some() { return Err(MALFORMED.into()); }
    Ok(worktrees)
}
