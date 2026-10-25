//! Git integration adapter. This adapter uses OS/Git effects and is outside
//! the current Aeneas pure-core proof boundary.
#[cfg(not(unix))]
compile_error!("transcrypt-v3 POC requires Unix for 0600/0700 local credential permissions");

use std::{
    env, fs,
    ffi::{OsStr, OsString},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
};
#[cfg(unix)]
use std::os::unix::{ffi::{OsStrExt, OsStringExt}, fs::OpenOptionsExt};
use zeroize::Zeroizing;
mod fsat;
mod session;
use session::Operation;
use transcrypt_v3::{initialize_config, unlock_config};
use transcrypt_v3_core::{
    check_attr_response_ok, hydrate_action, lock_action, parse_index_entry, HydrateAction, LockAction,
    MAX_RECORD, SALT_LEN,
};

const ATTRS: &[u8] = b"*.secret filter=transcrypt-v3 -diff\n";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("transcrypt-v3: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    // Git substitutes `%f` as a single shell-quoted argument. Preserve raw
    // Unix pathname bytes: env::args() would reject valid non-UTF8 Git paths.
    let args: Vec<OsString> = env::args_os().skip(1).collect();
    let action = args.first().and_then(|x| x.to_str()).ok_or(USAGE)?;
    if matches!(action, "help" | "--help" | "-h") {
        println!("{HELP}");
        return Ok(());
    }
    session::harden_process()?;
    let root = repo_root()?;
    // All v3 paths, including the agent's short relative socket address,
    // are interpreted from the repository root.
    env::set_current_dir(&root).map_err(|_| "cannot enter repository root")?;
    match action {
        "status" => {
            if args.len() != 1 { return Err("status takes no arguments".into()); }
            status(&root)
        },
        "init" | "unlock" => {
            if args.len() > 2 || (args.len() == 2 && args[1].to_str() != Some("--password-stdin")) {
                return Err("init/unlock accept only optional --password-stdin".into());
            }
            let password = passphrase(args.len() == 2)?;
            if action == "init" { init(&root, password) } else { unlock(&root, password) }
        },
        "clean" | "smudge" => {
            if args.len() != 2 { return Err("Git filter requires exactly one %f pathname".into()); }
            filter(&root, action == "clean", args[1].as_bytes())
        },
        "lock" | "verify-index" | "hydrate" | "serve" => {
            if args.len() != 1 { return Err("unexpected operation arguments".into()); }
            match action {
                "lock" => lock(&root),
                "verify-index" => verify_index(&root),
                "hydrate" => hydrate(&root),
                "serve" => session::serve(&root, &load_config(&root)?),
                _ => unreachable!(),
            }
        },
        _ => Err(format!("unknown v3 operation; {USAGE}")),
    }
}

const USAGE: &str = "usage: transcrypt-v3 init|unlock|hydrate|status|verify-index|lock|help \
    (clean/smudge <git-path> are invoked by Git)";

const HELP: &str = "\
transcrypt-v3: authenticated, path-bound encryption of *.secret files in Git.

Typical workflow
  transcrypt-v3 init        create .transcrypt/config, filters and hook; then commit
                            .transcrypt/config and .gitattributes
  transcrypt-v3 unlock      authenticate the passphrase and start the in-memory key agent
  transcrypt-v3 hydrate     decrypt the staged *.secret files into the worktree
                            (needed once after cloning or unlocking a locked checkout)
  transcrypt-v3 status      show lock state and each protected file's worktree state
  transcrypt-v3 verify-index
                            check every staged *.secret is ciphertext for its own path
                            (also run by the installed pre-commit hook)
  transcrypt-v3 lock        replace plaintext by the committed ciphertext and stop the agent;
                            refuses if any protected file has uncommitted changes

Options
  --password-stdin          (init, unlock) read the passphrase from stdin instead of the terminal

Files matching *.secret are encrypted with AES-256-SIV under a key derived by
Argon2id; each record is bound to the repository config and its exact Git path.
Renaming a protected file re-encrypts it. Equal plaintexts at the same path give
equal ciphertexts. See docs/verification/V3-USER-GUIDE.md.";

/// Read-only summary for users. Never decrypts unless the agent is live,
/// and never writes to the worktree, index or credential directory.
fn status(root: &Path) -> Result<(), String> {
    let config = match load_config(root) {
        Ok(config) => config,
        Err(e) => {
            println!("repository: not initialized for v3 ({e})");
            return Ok(());
        }
    };
    let unlocked = session::request(root, &config, Operation::Ping, &[], &[]).is_ok();
    println!("repository: v3 config {}", hex(&transcrypt_v3::config_id(&config)[..4]));
    println!("session:    {}", if unlocked { "unlocked (in-memory key agent running)" } else { "locked" });
    let mut counts = [0usize; 4];
    let mut exposed = 0usize;
    for (regular, path) in indexed_files(root)? {
        if !protected_path(&path) { continue; }
        let name = String::from_utf8_lossy(&path).into_owned();
        let state = (|| -> Result<&str, String> {
            if !regular { return Ok("unsupported mode"); }
            let object = git_show(root, &path)?;
            let target = open_protected(root, &indexed_path(&path)?)?;
            let worktree = target.read()?;
            if worktree == object { return Ok("ciphertext"); }
            if target.readable_by_others()? { exposed += 1; }
            if !unlocked { return Ok("modified or plaintext"); }
            let plaintext = session::request(root, &config, Operation::Decrypt, &path, &object)?;
            Ok(if worktree == plaintext { "plaintext" } else { "modified" })
        })().unwrap_or("error");
        counts[match state { "ciphertext" => 0, "plaintext" => 1, "modified" | "modified or plaintext" => 2, _ => 3 }] += 1;
        println!("  {state:<22} {name}");
    }
    println!("protected:  {} ciphertext, {} plaintext, {} modified, {} other",
        counts[0], counts[1], counts[2], counts[3]);
    if exposed > 0 {
        println!("warning:    {exposed} decrypted *.secret file(s) are readable by other users; \
            run `chmod go-rwx` on them and use `umask 077` in this checkout");
    }
    let untracked = git(root, &["ls-files", "--others", "--exclude-standard", "-z"])?;
    let loose = untracked.split(|b| *b == 0).filter(|p| protected_path(p)).count();
    if loose > 0 {
        println!("warning:    {loose} untracked *.secret file(s); `git add` them or lock will refuse");
    }
    if unlocked && counts[0] > 0 {
        println!("hint:       run `transcrypt-v3 hydrate` to decrypt ciphertext in the worktree");
    }
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn output(mut command: Command) -> Result<Vec<u8>, String> {
    let desc = format!("{:?}", command);
    let result = command.output().map_err(|e| format!("cannot run {desc}: {e}"))?;
    if !result.status.success() {
        return Err(format!("Git command failed ({desc}): {}", String::from_utf8_lossy(&result.stderr)));
    }
    Ok(result.stdout)
}

fn git(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = Command::new("git");
    command.current_dir(root).args(arguments);
    output(command)
}

fn repo_root() -> Result<PathBuf, String> {
    let mut command = Command::new("git");
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

fn config_path(root: &Path) -> Result<PathBuf, String> {
    let dir = root.join(".transcrypt");
    let meta = fs::symlink_metadata(&dir).map_err(|_| "missing .transcrypt directory: run init or clone a v3 repository")?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err("unsafe .transcrypt directory".into());
    }
    let file = dir.join("config");
    let fmeta = fs::symlink_metadata(&file).map_err(|_| "missing committed .transcrypt/config")?;
    if !fmeta.is_file() || fmeta.file_type().is_symlink() {
        return Err("unsafe .transcrypt/config type".into());
    }
    Ok(file)
}

fn load_config(root: &Path) -> Result<Vec<u8>, String> {
    let bytes = fs::read(config_path(root)?).map_err(|e| format!("cannot read v3 config: {e}"))?;
    transcrypt_v3_core::parse_config(&bytes).map_err(|_| "invalid v3 config grammar")?;
    Ok(bytes)
}

fn passphrase(from_stdin: bool) -> Result<Zeroizing<Vec<u8>>, String> {
    let bytes = if from_stdin {
        let mut value = Vec::new();
        io::stdin().take(4097).read_to_end(&mut value).map_err(|_| "cannot read passphrase from stdin")?;
        if value.len() > 4096 {
            return Err("passphrase too long".into());
        }
        if value.last() == Some(&b'\n') { value.pop(); }
        if value.last() == Some(&b'\r') { value.pop(); }
        value
    } else {
        rpassword::prompt_password("Transcrypt v3 passphrase: ")
            .map_err(|e| format!("cannot read terminal passphrase: {e}"))?
            .into_bytes()
    };
    if bytes.len() < 16 { return Err("v3 requires a passphrase of at least 16 bytes".into()); }
    Ok(Zeroizing::new(bytes))
}

fn shell_quote(text: &str) -> String {
    format!("'{}'", text.replace('\'', "'\\''"))
}

fn install_filters(root: &Path) -> Result<(), String> {
    let bin = env::current_exe().map_err(|_| "cannot resolve current executable")?;
    let path = bin.to_str().ok_or("executable path must be UTF-8")?;
    let program = shell_quote(path);
    for (k, value) in [
        ("filter.transcrypt-v3.clean", format!("{program} clean %f")),
        ("filter.transcrypt-v3.smudge", format!("{program} smudge %f")),
        ("filter.transcrypt-v3.required", "true".into()),
    ] {
        git(root, &["config", "--local", k, &value])?;
    }
    Ok(())
}

fn expected_hook() -> Result<String, String> {
    let bin = env::current_exe().map_err(|_| "cannot locate executable")?;
    let b = bin.to_str().ok_or("executable path must be UTF-8")?;
    Ok(format!("#!/bin/sh\nexec {} verify-index\n", shell_quote(b)))
}

fn check_hook_available(root: &Path) -> Result<(), String> {
    let path = root.join(".git/hooks/pre-commit");
    match fs::symlink_metadata(&path) {
        Ok(meta) => {
            if !meta.is_file() || meta.file_type().is_symlink() ||
                fs::read_to_string(&path).map_err(|_| "cannot read existing pre-commit hook")? != expected_hook()? {
                return Err("pre-commit hook already exists and is not this v3 hook; refuse to override".into());
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err("cannot inspect hook directory".into()),
    }
    Ok(())
}

fn install_hook(root: &Path) -> Result<(), String> {
    let path = root.join(".git/hooks/pre-commit");
    if path.exists() { return check_hook_available(root); }
    let script = expected_hook()?;
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o700);
    options.open(path).map_err(|e| format!("cannot install hook: {e}"))?
        .write_all(script.as_bytes()).map_err(|e| format!("cannot write hook: {e}"))?;
    Ok(())
}

/// An installation error must not leave a live key agent behind. The
/// file/index changes of initialization still require explicit recovery on
/// failure; this is not a filesystem-wide atomic transaction.
fn activate_session(root: &Path, config: &[u8], key: &transcrypt_v3::SecretKey, stage: bool) -> Result<(), String> {
    session::start(root, config, key)?;
    let result: Result<(), String> = (|| {
        install_filters(root)?;
        install_hook(root)?;
        if stage { git(root, &["add", "--", ".transcrypt/config", ".gitattributes"])?; }
        Ok(())
    })();
    if result.is_err() { let _ = session::stop(root, config); }
    result
}

fn init(root: &Path, password: Zeroizing<Vec<u8>>) -> Result<(), String> {
    let dir = root.join(".transcrypt");
    if fs::symlink_metadata(&dir).is_ok() {
        return Err(".transcrypt directory already exists; init requires a fresh v3 setup".into());
    }
    if fs::symlink_metadata(root.join(".gitattributes")).is_ok() {
        return Err(".gitattributes already exists; this POC requires a new attributes policy".into());
    }
    check_hook_available(root)?;
    let hook_preexisted = fs::symlink_metadata(root.join(".git/hooks/pre-commit")).is_ok();
    let mut salt = [0u8; SALT_LEN];
    getrandom::fill(&mut salt).map_err(|_| "OS randomness unavailable")?;
    let (config, key) = initialize_config(&password, &salt)?;
    let result = (|| -> Result<(), String> {
        fs::create_dir(&dir).map_err(|e| format!("cannot create .transcrypt: {e}"))?;
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        options.open(dir.join("config")).map_err(|e| format!("cannot create config: {e}"))?
            .write_all(&config).map_err(|e| format!("cannot write config: {e}"))?;
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        options.open(root.join(".gitattributes")).map_err(|e| format!("cannot create attributes: {e}"))?
            .write_all(ATTRS).map_err(|e| format!("cannot write attributes: {e}"))?;
        activate_session(root, &config, &key, true)
    })();
    if let Err(e) = result {
        rollback_init(root, &config, hook_preexisted);
        return Err(format!("{e}; initialization rolled back"));
    }
    eprintln!("Initialized v3; commit public metadata. Key lives only in the private credential agent until lock.");
    Ok(())
}

/// Undo exactly what a failed `init` created, so it can simply be rerun:
/// staged metadata, the files it wrote (only if unchanged), its hook (only
/// if it did not exist before) and its filter configuration.
fn rollback_init(root: &Path, config: &[u8], hook_preexisted: bool) {
    let _ = git(root, &["reset", "-q", "--", ".transcrypt/config", ".gitattributes"]);
    if fs::read(root.join(".gitattributes")).ok().as_deref() == Some(ATTRS) {
        let _ = fs::remove_file(root.join(".gitattributes"));
    }
    if fs::read(root.join(".transcrypt/config")).ok().as_deref() == Some(config) {
        let _ = fs::remove_file(root.join(".transcrypt/config"));
    }
    let _ = fs::remove_dir(root.join(".transcrypt"));
    let hook = root.join(".git/hooks/pre-commit");
    if !hook_preexisted && fs::read_to_string(&hook).ok() == expected_hook().ok() {
        let _ = fs::remove_file(&hook);
    }
    let _ = git(root, &["config", "--local", "--remove-section", "filter.transcrypt-v3"]);
}

fn unlock(root: &Path, password: Zeroizing<Vec<u8>>) -> Result<(), String> {
    let config = load_config(root)?;
    let key = unlock_config(&password, &config)?; // Authenticate BEFORE any persistent writes.
    check_hook_available(root)?;
    activate_session(root, &config, &key, false)?;
    eprintln!("Unlocked v3 via a private in-memory credential agent. For fresh clones run `transcrypt-v3 hydrate`.");
    Ok(())
}

fn lock(root: &Path) -> Result<(), String> {
    // Every tracked secret must match the encrypted index BEFORE any worktree rewrite.
    // If anything is dirty or untracked, do not remove credentials.
    verify_index(root)?;
    let untracked = git(root, &["ls-files", "--others", "-z"])?;
    if untracked.split(|b| *b == 0).any(protected_path) {
        return Err("untracked *.secret files exist; refusing to leave unprotected plaintext behind".into());
    }
    let config = load_config(root)?;
    session::request(root, &config, Operation::Ping, &[], &[])?;
    let mut to_flush = Vec::new();
    for (regular, path) in indexed_files(root)? {
        if !protected_path(&path) { continue; }
        if !regular {
            return Err("protected staged object is not a regular file".into());
        }
        let relative = indexed_path(&path)?;
        let target = open_protected(root, &relative)?;
        let source = target.read()?;
        let object = git_show(root, &path)?;
        // Only the agent holds the key, so it reseals; the verified core decides.
        let resealed = if source == object { Vec::new() } else {
            session::request(root, &config, Operation::Encrypt, &path, &source)?
        };
        match lock_action(&source, &object, &resealed) {
            Ok(LockAction::Keep) => {},
            Ok(LockAction::Flush) => to_flush.push((target, object)),
            Err(_) => return Err("protected worktree has uncommitted plaintext changes; refusing lock".into()),
        }
    }
    // Write only ciphertext via private staged files and atomic rename. A
    // crash can leave some files flushed and others plaintext; the key stays
    // in the agent until every rename succeeds, and rerunning `lock` resumes
    // (already-flushed files are `LockAction::Keep`). No secure erasure claim.
    let staging = staging_dir(root)?;
    for (i, (target, object)) in to_flush.iter().enumerate() {
        target.replace(&staging, object, i)?;
    }
    session::stop(root, &config)?;
    eprintln!("Locked: tracked *.secret files flushed and the in-memory credential agent stopped. This does not securely erase historical plaintext backups.");
    Ok(())
}

fn read_limited<R: Read>(read: R, limit: usize) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    read.take((limit as u64) + 1).read_to_end(&mut out).map_err(|_| "cannot read input")?;
    if out.len() > limit { return Err("v3 filter input exceeds supported size".into()); }
    Ok(out)
}

fn filter(root: &Path, clean: bool, git_path: &[u8]) -> Result<(), String> {
    transcrypt_v3::validate_protected_path(git_path)?;
    let config = load_config(root)?;
    let input = read_limited(io::stdin(), MAX_RECORD)?;
    // The verified core's `seal_record` refuses inputs that already are v3
    // records (double encryption), and `open_record` releases plaintext only
    // after authenticating it under this config and exact Git path.
    let result = if clean {
        session::request(root, &config, Operation::Encrypt, git_path, &input)?
    } else {
        session::request(root, &config, Operation::Decrypt, git_path, &input)?
    };
    io::stdout().write_all(&result).map_err(|_| "cannot write output")?;
    Ok(())
}

fn git_show(root: &Path, path: &[u8]) -> Result<Vec<u8>, String> {
    let mut query = Vec::with_capacity(path.len() + 1);
    query.push(b':');
    query.extend_from_slice(path);
    let mut command = Command::new("git");
    command.current_dir(root).arg("show");
    #[cfg(unix)]
    command.arg(std::ffi::OsString::from_vec(query));
    #[cfg(not(unix))]
    command.arg(String::from_utf8(query).map_err(|_| "non-UTF8 path unsupported here")?);
    output(command)
}

fn indexed_path(path: &[u8]) -> Result<PathBuf, String> {
    #[cfg(unix)]
    let relative = PathBuf::from(std::ffi::OsString::from_vec(path.to_vec()));
    #[cfg(not(unix))]
    let relative = PathBuf::from(String::from_utf8(path.to_vec()).map_err(|_| "non-UTF8 path unsupported")?);
    if relative.is_absolute() || relative.components().any(|c| matches!(c, std::path::Component::ParentDir | std::path::Component::RootDir)) {
        return Err("unsafe protected relative path".into());
    }
    Ok(relative)
}

/// A protected worktree file resolved race-free: its parent directory is
/// held open, every component having been opened with `O_NOFOLLOW`.
struct Protected {
    dir: fsat::Dir,
    leaf: OsString,
}

/// Resolve a Git-relative path below the repository root, refusing symlinks
/// and non-directories in *every* component and a non-regular leaf.
fn open_protected(root: &Path, relative: &Path) -> Result<Protected, String> {
    let parts: Vec<_> = relative.components().collect();
    let Some((leaf, parents)) = parts.split_last() else {
        return Err("empty protected worktree path".into());
    };
    let mut dir = fsat::Dir::open(root).map_err(|_| "cannot open repository root")?;
    for part in parents {
        let std::path::Component::Normal(name) = part else {
            return Err("unsafe protected path component".into());
        };
        dir = dir.subdir(name).map_err(|_| "protected worktree parent is missing, a symlink or not a directory")?;
    }
    let std::path::Component::Normal(leaf) = leaf else {
        return Err("unsafe protected path component".into());
    };
    let (regular, link) = dir.entry_kind(leaf).map_err(|_| "protected worktree path missing")?;
    if link { return Err("symlink in protected path rejected".into()); }
    if !regular { return Err("protected worktree entry is not a regular file".into()); }
    Ok(Protected { dir, leaf: leaf.to_os_string() })
}

impl Protected {
    /// Whether group or other users may read the file.
    fn readable_by_others(&self) -> Result<bool, String> {
        use std::os::unix::fs::PermissionsExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        let mode = file.metadata().map_err(|_| "cannot stat protected worktree file")?.permissions().mode();
        Ok(mode & 0o044 != 0)
    }

    fn read(&self) -> Result<Vec<u8>, String> {
        let file = self.dir.open_regular(&self.leaf)
            .map_err(|_| "cannot read protected worktree file (missing, symlink or not regular)")?;
        read_limited(file, MAX_RECORD)
    }

    /// Replace the file by `contents` through an exclusive mode-0600 file in
    /// the private staging directory, fsync, `renameat` into the held parent
    /// directory, then fsync that directory. A cross-filesystem rename fails
    /// closed (EXDEV) without touching the file. Not a multi-file transaction.
    fn replace(&self, staging: &Staging, contents: &[u8], slot: usize) -> Result<(), String> {
        let temp = OsString::from(format!("{}-{slot}.tmp", std::process::id()));
        let mut file = staging.dir.create_new(&temp, 0o600)
            .map_err(|e| format!("cannot create private staged file: {e}"))?;
        let result = file.write_all(contents).and_then(|_| file.sync_all());
        drop(file);
        if let Err(e) = result {
            let _ = staging.dir.unlink(&temp);
            return Err(format!("cannot write private staged file: {e}"));
        }
        if let Err(e) = staging.dir.rename_to(&temp, &self.dir, &self.leaf) {
            let _ = staging.dir.unlink(&temp);
            return Err(format!("cannot replace protected worktree file: {e}"));
        }
        self.dir.sync().map_err(|e| format!("cannot sync protected file directory: {e}"))
    }
}

/// Stage-0 files with paths represented as raw bytes (no newline splitting).
/// Each record is parsed by the verified core (`parse_index_entry`): the
/// flag says whether the mode is exactly 100644, and the path is everything
/// after the first TAB. Unmerged and malformed records are refused.
fn indexed_files(root: &Path) -> Result<Vec<(bool, Vec<u8>)>, String> {
    let data = git(root, &["ls-files", "--stage", "-z"])?;
    let mut entries = Vec::new();
    for entry in data.split(|b| *b == 0).filter(|item| !item.is_empty()) {
        let parsed = parse_index_entry(entry)
            .map_err(|_| "malformed or unmerged Git index entry; resolve conflicts first")?;
        entries.push((parsed.regular, entry[parsed.path_start..].to_vec()));
    }
    Ok(entries)
}

fn protected_path(path: &[u8]) -> bool {
    transcrypt_v3_core::is_protected_path(path)
}

/// Check Git's *effective* staged filter policy, not just the contents of the
/// committed root .gitattributes file. Per-directory attributes and the
/// checkout-local .git/info/attributes take precedence over that file.
/// `--cached` evaluates staged .gitattributes, while -z/--stdin transports
/// exact path bytes, including newlines and non-UTF8 names.
fn verify_staged_filter_attributes(root: &Path, paths: &[&[u8]]) -> Result<(), String> {
    if paths.is_empty() { return Ok(()); }
    if paths.iter().any(|path| path.is_empty() || path.contains(&0)) {
        return Err("invalid indexed protected path".into());
    }
    let mut command = Command::new("git");
    command.current_dir(root)
        .args(["check-attr", "--cached", "-z", "--stdin", "filter"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut request = Vec::new();
    for path in paths {
        request.extend_from_slice(path);
        request.push(0);
    }
    let mut child = command.spawn().map_err(|_| "cannot run Git staged attribute check")?;
    {
        let mut stdin = child.stdin.take().ok_or("Git attribute input pipe missing")?;
        stdin.write_all(&request)
            .map_err(|_| "cannot send protected paths to Git attribute checker")?;
    }
    let result = child.wait_with_output()
        .map_err(|_| "cannot read Git staged attribute check")?;
    if !result.status.success() {
        return Err(format!("Git staged attribute check failed: {}",
            String::from_utf8_lossy(&result.stderr)));
    }
    if !check_attr_response_ok(&request, &result.stdout) {
        return Err("protected staged path does not have the required effective transcrypt-v3 filter".into());
    }
    Ok(())
}

fn verify_index(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    if git_show(root, b".transcrypt/config")? != config {
        return Err("staged .transcrypt/config is missing or differs from worktree".into());
    }
    if git_show(root, b".gitattributes")? != ATTRS {
        return Err("staged .gitattributes differs from required v3 policy".into());
    }
    session::request(root, &config, Operation::Ping, &[], &[])?;
    let entries = indexed_files(root)?;
    for (regular, path) in &entries {
        if (path.as_slice() == &b".transcrypt/config"[..] ||
            path.as_slice() == &b".gitattributes"[..]) && !*regular {
            return Err("public v3 metadata is not a regular staged file".into());
        }
    }
    let protected: Vec<_> = entries.iter()
        .filter(|(_, path)| protected_path(path))
        .map(|(_, path)| path.as_slice())
        .collect();
    // Fail before any decryption if the effective Git filter changed.
    verify_staged_filter_attributes(root, &protected)?;
    for (regular, path) in entries {
        if !protected_path(&path) { continue; }
        if !regular {
            return Err("protected path is not a regular file in staged index".into());
        }
        let encrypted = git_show(root, &path)?;
        session::request(root, &config, Operation::Decrypt, &path, &encrypted)?;
    }
    Ok(())
}

/// Private staging directory for whole-file replacements:
/// `.git/transcrypt-v3-staging`, a real mode-0700 directory held open by fd.
/// Temporaries never live in the worktree, so a crash cannot leave plaintext
/// where `git add` could commit it unencrypted, and Git never reads files
/// under `.git`. Anything left by an interrupted earlier run is ours and is
/// removed.
struct Staging {
    dir: fsat::Dir,
}

fn staging_dir(root: &Path) -> Result<Staging, String> {
    let git_dir = fsat::Dir::open(root).and_then(|r| r.subdir(OsStr::new(".git")))
        .map_err(|_| "cannot open .git directory")?;
    let name = OsStr::new("transcrypt-v3-staging");
    match git_dir.mkdir(name, 0o700) {
        Ok(()) => {},
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {},
        Err(e) => return Err(format!("cannot create private staging directory: {e}")),
    }
    let dir = git_dir.subdir(name)
        .map_err(|_| "unsafe .git/transcrypt-v3-staging; require a real 0700 directory")?;
    if dir.mode().map_err(|_| "cannot examine private staging directory")? & 0o077 != 0 {
        return Err("unsafe .git/transcrypt-v3-staging; require a real 0700 directory".into());
    }
    for entry in dir.entries().map_err(|_| "cannot list private staging directory")? {
        let (regular, _) = dir.entry_kind(&entry).map_err(|_| "cannot examine stale staged file")?;
        if !regular {
            return Err("unexpected entry in private staging directory".into());
        }
        dir.unlink(&entry).map_err(|e| format!("cannot remove stale staged file: {e}"))?;
    }
    Ok(Staging { dir })
}

fn hydrate(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    // Authenticate ALL staged protected objects and the staged metadata
    // before exposing any plaintext in the checkout.
    verify_index(root)?;
    let index_before = git(root, &["ls-files", "--stage", "-z"])?;
    let entries: Vec<_> = indexed_files(root)?.into_iter()
        .filter(|(_, path)| protected_path(path)).collect();
    let mut pending = Vec::new();

    // Validate the complete worktree first. A checkout may contain a mixture
    // of ciphertext and already-hydrated plaintext after an interrupted run.
    // Neither an unexpected third value nor a protected symlink is replaced.
    for (regular, path) in &entries {
        if !*regular { return Err("protected path is not regular".into()); }
        let object = git_show(root, path)?;
        let plaintext = session::request(root, &config, Operation::Decrypt, path, &object)?;
        let relative = indexed_path(path)?;
        let worktree = open_protected(root, &relative)?.read()?;
        match hydrate_action(&worktree, &object, &plaintext) {
            Ok(HydrateAction::Publish) => pending.push((path.clone(), relative)),
            Ok(HydrateAction::Keep) => {},
            Err(_) => return Err("protected worktree differs from staged ciphertext and authenticated plaintext; refusing overwrite".into()),
        }
    }
    // Detect a changed index or public configuration between validation and
    // publication. Concurrent changes during publication still require OS
    // isolation; they are explicitly outside this prototype's guarantees.
    if git(root, &["ls-files", "--stage", "-z"])? != index_before || load_config(root)? != config {
        return Err("index or public configuration changed during hydration".into());
    }

    let staging = staging_dir(root)?;
    for (i, (path, relative)) in pending.into_iter().enumerate() {
        let object = git_show(root, &path)?;
        let plaintext = session::request(root, &config, Operation::Decrypt, &path, &object)?;
        let target = open_protected(root, &relative)?;
        if target.read()? != object {
            return Err("protected worktree changed during hydration; refusing overwrite".into());
        }
        target.replace(&staging, &plaintext, i)?;
    }
    // Git's index still caches the size/mtime of the encrypted checkout.
    // `git add` is needed to refresh the worktree stat cache: merely having
    // equal clean-filter output may still report a modified working file.
    // The filter now receives only authenticated plaintext, never the raw
    // ciphertext that caused the original `git restore` failure. Verify that
    // re-staging changes NO staged blob or mode, even when index != HEAD.
    for (_, path) in &entries {
        let mut command = Command::new("git");
        command.current_dir(root).args(["add", "--"]);
        #[cfg(unix)]
        command.arg(std::ffi::OsString::from_vec(path.clone()));
        #[cfg(not(unix))]
        command.arg(String::from_utf8(path.clone()).map_err(|_| "non-UTF8 path unsupported")?);
        output(command)?;
    }
    if git(root, &["ls-files", "--stage", "-z"])? != index_before {
        return Err("hydration changed staged Git objects; refusing to report success".into());
    }
    eprintln!("Hydration complete.");
    Ok(())
}

#[cfg(test)]
mod local_path_tests {
    use super::*;

    #[test]
    fn replacement_is_private_and_leaves_no_worktree_temporaries() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = std::env::temp_dir().join(format!(
            "transcrypt-v3-replace-{}", std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(tmp.join(".git")).unwrap();
        let sdir = tmp.join(".git/transcrypt-v3-staging");
        drop(staging_dir(&tmp).unwrap());
        assert_eq!(fs::metadata(&sdir).unwrap().permissions().mode() & 0o777, 0o700);
        // A crash-leftover temporary is purged on the next use.
        fs::write(sdir.join("stale.tmp"), b"stale plaintext").unwrap();
        let staging = staging_dir(&tmp).unwrap();
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        let path = tmp.join("item.secret");
        fs::write(&path, b"ciphertext placeholder").unwrap();
        let target = open_protected(&tmp, Path::new("item.secret")).unwrap();
        target.replace(&staging, b"authenticated plaintext", 0).unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"authenticated plaintext");
        assert_eq!(fs::metadata(&path).unwrap().permissions().mode() & 0o077, 0);
        assert_eq!(fs::read_dir(&tmp).unwrap().count(), 2, "only .git and the file");
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        // A symlinked or loosely permissioned staging directory is refused.
        fs::remove_dir(&sdir).unwrap();
        std::os::unix::fs::symlink(&tmp, &sdir).unwrap();
        assert!(staging_dir(&tmp).is_err());
        fs::remove_file(&sdir).unwrap();
        fs::create_dir(&sdir).unwrap();
        fs::set_permissions(&sdir, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(staging_dir(&tmp).is_err());
        fs::remove_dir_all(&tmp).unwrap();
    }

    #[test]
    fn protected_parent_symlinks_cannot_redirect_lock_or_hydrate() {
        use std::os::unix::fs::symlink;
        let tmp = std::env::temp_dir().join(format!(
            "transcrypt-v3-parent-symlink-{}", std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir(&tmp).unwrap();
        let external = tmp.join("external");
        fs::create_dir(&external).unwrap();
        fs::write(external.join("item.secret"), b"test").unwrap();
        let checkout = tmp.join("checkout");
        fs::create_dir_all(checkout.join(".git")).unwrap();
        symlink(&external, checkout.join("linked")).unwrap();
        assert!(open_protected(&checkout, Path::new("linked/item.secret")).is_err());
        symlink(external.join("item.secret"), checkout.join("leaf.secret")).unwrap();
        assert!(open_protected(&checkout, Path::new("leaf.secret")).is_err());
        fs::create_dir(checkout.join("regular")).unwrap();
        fs::write(checkout.join("regular/item.secret"), b"test").unwrap();
        let target = open_protected(&checkout, Path::new("regular/item.secret")).unwrap();
        assert_eq!(target.read().unwrap(), b"test");
        // Race: after resolution, the parent is swapped for a symlink to an
        // outside directory. The held directory fd keeps the write inside.
        let staging = staging_dir(&checkout).unwrap();
        fs::rename(checkout.join("regular"), checkout.join("moved")).unwrap();
        symlink(&external, checkout.join("regular")).unwrap();
        target.replace(&staging, b"plaintext", 0).unwrap();
        assert_eq!(fs::read(external.join("item.secret")).unwrap(), b"test", "write escaped");
        assert_eq!(fs::read(checkout.join("moved/item.secret")).unwrap(), b"plaintext");
        let _ = fs::remove_dir_all(tmp);
    }
}
