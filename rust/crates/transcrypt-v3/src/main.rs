//! Git integration adapter. This adapter uses OS/Git effects and is outside
//! the current Aeneas pure-core proof boundary.
#[cfg(not(unix))]
compile_error!("transcrypt-v3 POC requires Unix for 0600/0700 local credential permissions");

use std::{
    collections::{HashMap, HashSet},
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
    check_attr_response_ok, hydrate_action, is_object_id, lock_action, parse_index_entry, record_envelope_ok,
    HydrateAction, LockAction, MAX_RECORD, SALT_LEN,
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
    if action == "audit" {
        // Also runs keyless in a bare repository (a server's pre-receive
        // hook), where there is no worktree and no agent.
        let (root, keyed) = match repo_root() {
            Ok(root) => (root, true),
            Err(_) => (env::current_dir().map_err(|_| "cannot read working directory")?, false),
        };
        env::set_current_dir(&root).map_err(|_| "cannot enter repository root")?;
        let audited = audit(&root, &args[1..], keyed)?;
        println!("audit: {} protected record(s) checked{}", audited.records,
            if audited.authenticated { ", all authenticated by the unlocked agent" }
            else { " (envelopes only: unlock to authenticate them)" });
        return Ok(());
    }
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
            let mut stdin = false;
            let mut auto_hydrate = true;
            for arg in &args[1..] {
                match arg.to_str() {
                    Some("--password-stdin") if !stdin => stdin = true,
                    Some("--no-hydrate") if action == "unlock" && auto_hydrate => auto_hydrate = false,
                    _ => return Err("init accepts --password-stdin; unlock accepts --password-stdin and --no-hydrate".into()),
                }
            }
            let password = passphrase(stdin)?;
            if action == "init" { init(&root, password) } else { unlock(&root, password, auto_hydrate) }
        },
        "clean" | "smudge" => {
            if args.len() != 2 { return Err("Git filter requires exactly one %f pathname".into()); }
            filter(&root, action == "clean", args[1].as_bytes())
        },
        "pre-push" => {
            if args.len() > 3 { return Err("pre-push takes the remote name and URL".into()); }
            pre_push(&root, args.get(1).map(OsString::as_os_str))
        },
        "lock" | "verify-index" | "hydrate" | "serve" => {
            if args.len() != 1 { return Err("unexpected operation arguments".into()); }
            match action {
                "lock" => lock(&root),
                "verify-index" => verify_index_command(&root),
                "hydrate" => hydrate(&root),
                "serve" => session::serve(&root, &load_config(&root)?),
                _ => unreachable!(),
            }
        },
        _ => Err(format!("unknown v3 operation; {USAGE}")),
    }
}

const USAGE: &str = "usage: transcrypt-v3 init|unlock|hydrate|status|verify-index|audit|lock|help \
    (clean/smudge <git-path> and pre-push are invoked by Git)";

const HELP: &str = "\
transcrypt-v3: authenticated, path-bound encryption of *.secret files in Git.

Typical workflow
  transcrypt-v3 init        create .transcrypt/config, filters and hook; then commit
                            .transcrypt/config and .gitattributes
  transcrypt-v3 unlock      authenticate the passphrase, start the in-memory key agent and
                            decrypt the staged *.secret files (skip with --no-hydrate)
  transcrypt-v3 hydrate     decrypt the staged *.secret files into the worktree
                            (only needed after `unlock --no-hydrate` or a refused hydration)
  transcrypt-v3 status      show lock state and each protected file's worktree state
  transcrypt-v3 verify-index
                            check every staged *.secret is ciphertext for its own path
                            (also run by the installed pre-commit hook; while locked it
                            checks record envelopes only)
  transcrypt-v3 audit [<rev-list args>]
                            check every *.secret in the given commits (default HEAD) is a
                            v3 record, without the key; authenticates them when unlocked.
                            The installed pre-push hook runs it on the commits being
                            pushed; run it in CI or a server hook to catch plaintext pushed
                            from checkouts that never ran unlock
  transcrypt-v3 lock        replace plaintext by the committed ciphertext and stop the agent;
                            refuses if any protected file has uncommitted changes

Options
  --password-stdin          (init, unlock) read the passphrase from stdin instead of the terminal
  --no-hydrate              (unlock) leave ciphertext in the worktree

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
    for staged in indexed_files(root)? {
        if !protected_path(&staged.path) { continue; }
        let name = String::from_utf8_lossy(&staged.path).into_owned();
        let state = (|| -> Result<&str, String> {
            if !staged.regular { return Ok("unsupported mode"); }
            let object = git_blob(root, &staged.oid)?;
            let target = open_protected(root, &indexed_path(&staged.path)?)?;
            let (worktree, _) = target.read()?;
            if *worktree == object { return Ok("ciphertext"); }
            if target.readable_by_others()? { exposed += 1; }
            if !unlocked { return Ok("modified or plaintext"); }
            let plaintext = session::request(root, &config, Operation::Decrypt, &staged.path, &object)?;
            Ok(if *worktree == *plaintext { "plaintext" } else { "modified" })
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
    // Protection is exactly the lowercase suffix `.secret`.
    let tracked = git(root, &["ls-files", "-z"])?;
    for path in tracked.split(|b| *b == 0).chain(untracked.split(|b| *b == 0)) {
        if !protected_path(path) && (path.to_ascii_lowercase().ends_with(b".secret") || plaintext_copy_name(path)) {
            println!("warning:    {} is NOT encrypted (only names ending in lowercase .secret are)",
                String::from_utf8_lossy(path));
        }
    }
    if unlocked && counts[0] > 0 {
        println!("hint:       run `transcrypt-v3 hydrate` to decrypt ciphertext in the worktree");
    }
    if hooks_bypassed(root) {
        println!("warning:    {HOOKS_BYPASSED}");
    }
    Ok(())
}

const HOOKS_BYPASSED: &str = "core.hooksPath is set, so Git does not run the v3 pre-commit and \
    pre-push checks installed in .git/hooks";

/// Whether Git is configured to run hooks from somewhere other than
/// `.git/hooks`, where v3 installs its checks.
fn hooks_bypassed(root: &Path) -> bool {
    git(root, &["config", "core.hooksPath"]).map(|v| !v.trim_ascii().is_empty()).unwrap_or(false)
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

/// Every Git subprocess. Pathspecs are literal, so a tracked file named
/// `[a].secret` or `:(glob)*` can never select other files, and replace
/// refs are ignored, so an object id names exactly the bytes hashed into it.
fn git_command(root: Option<&Path>) -> Command {
    let mut command = Command::new("git");
    if let Some(root) = root { command.current_dir(root); }
    command.env("GIT_LITERAL_PATHSPECS", "1").env("GIT_NO_REPLACE_OBJECTS", "1");
    command
}

fn git(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = git_command(Some(root));
    command.args(arguments);
    output(command)
}

fn git_with_input(root: &Path, arguments: &[&str], input: &[u8]) -> Result<Vec<u8>, String> {
    let mut child = git_command(Some(root))
        .args(arguments)
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
        .spawn().map_err(|e| format!("cannot run git {}: {e}", arguments.join(" ")))?;
    // Feed the input from another thread: Git may fill its output pipe
    // before it has read all of a large input.
    let mut stdin = child.stdin.take().ok_or("Git input pipe missing")?;
    let input = input.to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let result = child.wait_with_output().map_err(|_| "cannot wait for Git")?;
    let written = writer.join().map_err(|_| "Git input writer failed")?;
    if written.is_err() || !result.status.success() {
        return Err(format!("Git command failed (git {}): {}", arguments.join(" "),
            String::from_utf8_lossy(&result.stderr)));
    }
    Ok(result.stdout)
}

fn repo_root() -> Result<PathBuf, String> {
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
    // Preallocated and wrapped before reading, so the buffer never grows
    // (leaving unwiped copies) and every exit path wipes it.
    let bytes = if from_stdin {
        let mut value = Zeroizing::new(Vec::with_capacity(4098));
        io::stdin().take(4097).read_to_end(&mut value).map_err(|_| "cannot read passphrase from stdin")?;
        if value.len() > 4096 {
            return Err("passphrase too long".into());
        }
        if value.last() == Some(&b'\n') { value.pop(); }
        if value.last() == Some(&b'\r') { value.pop(); }
        value
    } else {
        Zeroizing::new(rpassword::prompt_password("Transcrypt v3 passphrase: ")
            .map_err(|e| format!("cannot read terminal passphrase: {e}"))?
            .into_bytes())
    };
    if bytes.len() < 16 { return Err("v3 requires a passphrase of at least 16 bytes".into()); }
    Ok(bytes)
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

/// Hooks installed by init and unlock, with the v3 command each runs:
/// verify the staged index before every commit, and audit the commits being
/// pushed (which also covers merges, rebases, cherry-picks and
/// `--no-verify` commits that never ran the pre-commit hook).
const HOOKS: [(&str, &str); 2] = [("pre-commit", "verify-index"), ("pre-push", "pre-push \"$@\"")];

fn expected_hook(command: &str) -> Result<String, String> {
    let bin = env::current_exe().map_err(|_| "cannot locate executable")?;
    let b = bin.to_str().ok_or("executable path must be UTF-8")?;
    Ok(format!("#!/bin/sh\nexec {} {command}\n", shell_quote(b)))
}

fn hook_path(root: &Path, name: &str) -> PathBuf {
    root.join(".git/hooks").join(name)
}

fn check_hook_available(root: &Path) -> Result<(), String> {
    for (name, command) in HOOKS {
        let path = hook_path(root, name);
        match fs::symlink_metadata(&path) {
            Ok(meta) => {
                if !meta.is_file() || meta.file_type().is_symlink() ||
                    fs::read_to_string(&path).map_err(|_| format!("cannot read existing {name} hook"))? != expected_hook(command)? {
                    return Err(format!("{name} hook already exists and is not this v3 hook; refuse to override"));
                }
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(_) => return Err("cannot inspect hook directory".into()),
        }
    }
    Ok(())
}

fn install_hook(root: &Path) -> Result<(), String> {
    check_hook_available(root)?;
    for (name, command) in HOOKS {
        let path = hook_path(root, name);
        if fs::symlink_metadata(&path).is_ok() { continue; }
        let script = expected_hook(command)?;
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o700);
        options.open(path).map_err(|e| format!("cannot install {name} hook: {e}"))?
            .write_all(script.as_bytes()).map_err(|e| format!("cannot write {name} hook: {e}"))?;
    }
    if hooks_bypassed(root) {
        eprintln!("warning: {HOOKS_BYPASSED}");
    }
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
        exclude_plaintext_copies(root)?;
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
    // Files already tracked as `*.secret` are plaintext in the index (and in
    // history): enabling v3 would not encrypt them and would only appear to.
    let mut tracked: Vec<Vec<u8>> = indexed_files(root)?.into_iter().map(|e| e.path).collect();
    if git(root, &["rev-parse", "-q", "--verify", "HEAD^{commit}"]).is_ok() {
        tracked.extend(tree_files(root, "HEAD")?.into_iter().map(|e| e.path));
    }
    if let Some(path) = tracked.iter().find(|p| protected_path(p)) {
        return Err(format!("{} is already tracked unencrypted; remove *.secret files from the index \
            and history (and rotate their secrets) before enabling v3", String::from_utf8_lossy(path)));
    }
    let hook_preexisted = HOOKS.map(|(name, _)| fs::symlink_metadata(hook_path(root, name)).is_ok());
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
fn rollback_init(root: &Path, config: &[u8], hook_preexisted: [bool; HOOKS.len()]) {
    let _ = git(root, &["reset", "-q", "--", ".transcrypt/config", ".gitattributes"]);
    if fs::read(root.join(".gitattributes")).ok().as_deref() == Some(ATTRS) {
        let _ = fs::remove_file(root.join(".gitattributes"));
    }
    if fs::read(root.join(".transcrypt/config")).ok().as_deref() == Some(config) {
        let _ = fs::remove_file(root.join(".transcrypt/config"));
    }
    let _ = fs::remove_dir(root.join(".transcrypt"));
    for ((name, command), preexisted) in HOOKS.into_iter().zip(hook_preexisted) {
        let hook = hook_path(root, name);
        if !preexisted && fs::read_to_string(&hook).ok() == expected_hook(command).ok() {
            let _ = fs::remove_file(&hook);
        }
    }
    let _ = git(root, &["config", "--local", "--remove-section", "filter.transcrypt-v3"]);
}

fn unlock(root: &Path, password: Zeroizing<Vec<u8>>, auto_hydrate: bool) -> Result<(), String> {
    let config = load_config(root)?;
    let key = unlock_config(&password, &config)?; // Authenticate BEFORE any persistent writes.
    check_hook_available(root)?;
    activate_session(root, &config, &key, false)?;
    if !auto_hydrate {
        eprintln!("Unlocked v3 via a private in-memory credential agent. Run `transcrypt-v3 hydrate` to decrypt the worktree.");
        return Ok(());
    }
    // Unlocking is complete; hydration is a separate, all-or-nothing step
    // whose refusal must not hide the fact that the agent is now running.
    match hydrate(root) {
        Ok(()) => eprintln!("Unlocked v3 and decrypted the protected worktree files."),
        Err(e) => eprintln!("Unlocked v3, but hydration changed nothing: {e}\n\
            Inspect with `transcrypt-v3 status`, then run `transcrypt-v3 hydrate`."),
    }
    Ok(())
}

fn lock(root: &Path) -> Result<(), String> {
    let staging = staging_dir(root)?;
    // Every tracked secret must match the encrypted index BEFORE any worktree rewrite.
    // If anything is dirty or untracked, do not remove credentials.
    let verified = verify_index(root)?;
    let untracked = git(root, &["ls-files", "--others", "-z"])?;
    if untracked.split(|b| *b == 0).any(protected_path) {
        return Err("untracked *.secret files exist; refusing to leave unprotected plaintext behind".into());
    }
    let config = load_config(root)?;
    let mut to_flush = Vec::new();
    for staged in &verified.protected {
        let relative = indexed_path(&staged.path)?;
        let target = open_protected(root, &relative)?;
        let (source, stamp) = target.read()?;
        // The object the index named when it was verified, by object id.
        let object = git_blob(root, &staged.oid)?;
        // Only the agent holds the key, so it reseals; the verified core decides.
        let resealed = if *source == object { Zeroizing::new(Vec::new()) } else {
            session::request(root, &config, Operation::Encrypt, &staged.path, &source)?
        };
        match lock_action(&source, &object, &resealed) {
            Ok(LockAction::Keep) => {},
            Ok(LockAction::Flush) => {
                if target.links()? > 1 {
                    eprintln!("warning: {} has other hard links; they keep its plaintext after lock",
                        String::from_utf8_lossy(&staged.path));
                }
                to_flush.push((relative, object, stamp));
            },
            Err(_) => return Err("protected worktree has uncommitted plaintext changes; refusing lock".into()),
        }
    }
    // Write only ciphertext via private staged files and atomic rename. A
    // crash can leave some files flushed and others plaintext; the key stays
    // in the agent until every rename succeeds, and rerunning `lock` resumes
    // (already-flushed files are `LockAction::Keep`). A file changed after it
    // was checked is refused, not overwritten. No secure erasure claim.
    for (i, (relative, object, stamp)) in to_flush.iter().enumerate() {
        open_protected(root, relative)?.replace(&staging, object, i, stamp)?;
    }
    // While the agent still runs, refresh Git's cached stat data for the
    // ciphertext now in the worktree (the clean filter returns an authentic
    // record unchanged), so a locked checkout is clean and `git commit -a`
    // does not need the key.
    reindex(root, &verified)?;
    session::stop(root, &config)?;
    eprintln!("Locked: tracked *.secret files flushed and the in-memory credential agent stopped. This does not securely erase historical plaintext backups.");
    Ok(())
}

fn read_limited<R: Read>(read: R, limit: usize) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    read.take((limit as u64) + 1).read_to_end(&mut out).map_err(|_| "cannot read input")?;
    if out.len() > limit { return Err("input exceeds the 16 MiB v3 size limit".into()); }
    Ok(out)
}

fn filter(root: &Path, clean: bool, git_path: &[u8]) -> Result<(), String> {
    transcrypt_v3::validate_protected_path(git_path)?;
    let config = load_config(root)?;
    let input = Zeroizing::new(read_limited(io::stdin(), MAX_RECORD)?);
    if session::request(root, &config, Operation::Ping, &[], &[]).is_err() {
        // Locked (no agent serves this config): without the key neither
        // filter can change a record, so both pass a record envelope of
        // this configuration through unchanged and refuse anything else.
        // A locked checkout then behaves like a clone that was never
        // unlocked (ciphertext in the worktree), Git can re-clean it, and
        // plaintext is still never stored. Authenticity is checked when
        // unlocked (verify-index, hydrate, audit).
        if !record_envelope_ok(&input, &transcrypt_v3::config_id(&config)) {
            return Err("v3 session is locked; run unlock".into());
        }
        io::stdout().write_all(&input).map_err(|_| "cannot write output")?;
        return Ok(());
    }
    // The agent's clean returns a record that already opens at this path
    // unchanged and otherwise seals with the verified core's `seal_record`,
    // which refuses any other v3 record (double encryption); `open_record`
    // releases plaintext only after authenticating it under this config and
    // exact Git path.
    let result = if clean {
        session::request(root, &config, Operation::Encrypt, git_path, &input)?
    } else {
        session::request(root, &config, Operation::Decrypt, git_path, &input)?
    };
    io::stdout().write_all(&result).map_err(|_| "cannot write output")?;
    Ok(())
}

/// The content of one Git blob, named by an id the verified core accepted
/// (never revision syntax such as `:path`, which reads `:0:x.secret` as stage
/// 0 of `x.secret`). Reads stop at the v3 size bound, so a hostile oversized
/// blob is refused without being loaded. All reads of one process share a
/// single `git cat-file --batch`.
fn git_blob(root: &Path, oid: &str) -> Result<Vec<u8>, String> {
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
        let size = header.strip_prefix(oid.as_bytes())
            .and_then(|rest| rest.strip_prefix(b" blob "))
            .and_then(|rest| rest.strip_suffix(b"\n"))
            .and_then(|digits| std::str::from_utf8(digits).ok())
            .and_then(|digits| digits.parse::<usize>().ok())
            .filter(|size| header == format!("{oid} blob {size}\n").as_bytes())
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

impl Drop for Objects {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
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
    /// Remove group and other permissions (through an `O_NOFOLLOW`
    /// descriptor, so a swapped-in symlink is never followed).
    fn make_private(&self) -> Result<(), String> {
        use std::os::unix::fs::PermissionsExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        let mode = file.metadata().map_err(|_| "cannot stat protected worktree file")?.permissions().mode();
        if mode & 0o077 != 0 {
            file.set_permissions(fs::Permissions::from_mode(mode & 0o700))
                .map_err(|_| "cannot restrict protected worktree file permissions")?;
        }
        Ok(())
    }

    /// Number of hard links to the file.
    fn links(&self) -> Result<u64, String> {
        use std::os::unix::fs::MetadataExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        Ok(file.metadata().map_err(|_| "cannot stat protected worktree file")?.nlink())
    }

    /// Whether group or other users may read the file.
    fn readable_by_others(&self) -> Result<bool, String> {
        use std::os::unix::fs::PermissionsExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        let mode = file.metadata().map_err(|_| "cannot stat protected worktree file")?.permissions().mode();
        Ok(mode & 0o044 != 0)
    }

    /// The contents and the stamp of the file they were read from.
    fn read(&self) -> Result<(Zeroizing<Vec<u8>>, fsat::Stamp), String> {
        let file = self.dir.open_regular(&self.leaf)
            .map_err(|_| "cannot read protected worktree file (missing, symlink or not regular)")?;
        let stamp = fsat::Stamp::of(&file).map_err(|_| "cannot stat protected worktree file")?;
        let contents = Zeroizing::new(read_limited(&file, MAX_RECORD)?);
        if fsat::Stamp::of(&file).map_err(|_| "cannot stat protected worktree file")? != stamp {
            return Err("protected worktree file changed while it was read".into());
        }
        Ok((contents, stamp))
    }

    /// Replace the file by `contents` through an exclusive mode-0600 file in
    /// the private staging directory, fsync, `renameat` into the held parent
    /// directory, then fsync that directory. The entry must still have the
    /// `expected` stamp of the read that justified the replacement, so an
    /// edit made since then is refused instead of being lost (a same-UID
    /// writer can still race the final check and the rename). A
    /// cross-filesystem rename fails closed (EXDEV) without touching the
    /// file. Not a multi-file transaction.
    fn replace(&self, staging: &Staging, contents: &[u8], slot: usize, expected: &fsat::Stamp) -> Result<(), String> {
        let temp = OsString::from(format!("{}-{slot}.tmp", std::process::id()));
        let mut file = staging.dir.create_new(&temp, 0o600)
            .map_err(|e| format!("cannot create private staged file: {e}"))?;
        let result = file.write_all(contents).and_then(|_| file.sync_all());
        drop(file);
        if let Err(e) = result {
            let _ = staging.dir.unlink(&temp);
            return Err(format!("cannot write private staged file: {e}"));
        }
        if self.dir.stamp(&self.leaf).ok().as_ref() != Some(expected) {
            let _ = staging.dir.unlink(&temp);
            return Err("protected worktree file changed after it was checked; refusing to replace it".into());
        }
        if let Err(e) = staging.dir.rename_to(&temp, &self.dir, &self.leaf) {
            let _ = staging.dir.unlink(&temp);
            return Err(format!("cannot replace protected worktree file: {e}"));
        }
        self.dir.sync().map_err(|e| format!("cannot sync protected file directory: {e}"))
    }
}

/// One stage-0 record of the index or of a commit's tree. Every later read
/// of its content goes through `oid`, so a concurrent index change cannot
/// substitute other bytes for the ones that were verified.
struct Staged {
    regular: bool,
    oid: String,
    path: Vec<u8>,
}

/// Parse NUL-separated `<mode> SP <oid> SP 0 TAB <path>` records, with paths
/// as raw bytes. Each record is parsed by the verified core
/// (`parse_index_entry`): the flag says whether the mode is exactly 100644,
/// and the path is everything after the first TAB. Its specification fixes
/// the record as `mode(6) SP oid SP "0" TAB path`, so the object id is
/// `entry[7..path_start - 3]` (Lean `indexRecord_oid`), which must also pass
/// `is_object_id`.
/// Unmerged and malformed records are refused.
fn parse_listing(data: &[u8]) -> Result<Vec<Staged>, String> {
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
fn tree_files(root: &Path, commit: &str) -> Result<Vec<Staged>, String> {
    let data = git(root, &["ls-tree", "-r", "-z", "--full-tree", commit])?;
    let mut listing = Vec::with_capacity(data.len());
    for entry in data.split(|b| *b == 0).filter(|item| !item.is_empty()) {
        let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed git ls-tree record")?;
        let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
        let [mode, _kind, oid] = fields[..] else { return Err("malformed git ls-tree record".into()) };
        listing.extend_from_slice(mode);
        listing.push(b' ');
        listing.extend_from_slice(oid);
        listing.extend_from_slice(b" 0");
        listing.extend_from_slice(&entry[tab..]);
        listing.push(0);
    }
    parse_listing(&listing)
}

fn indexed_files(root: &Path) -> Result<Vec<Staged>, String> {
    parse_listing(&git(root, &["ls-files", "--stage", "-z"])?)
}

fn protected_path(path: &[u8]) -> bool {
    transcrypt_v3_core::is_protected_path(path)
}

/// Names that editors and merge tools give to copies of a `*.secret` file.
/// Such copies hold plaintext but are not protected, so `git add -A` would
/// commit them unencrypted. A heuristic backstop, not a guarantee.
const COPY_SUFFIXES: [&[u8]; 10] = [
    b".secret~", b".secret.swp", b".secret.swo", b".secret.swx", b".secret.orig",
    b".secret.bak", b".secret.tmp", b".secret.rej", b".secret.save", b".secret#",
];

fn plaintext_copy_name(path: &[u8]) -> bool {
    COPY_SUFFIXES.iter().any(|suffix| path.ends_with(suffix))
}

/// Ignore those copies in this checkout (`.git/info/exclude`, never committed).
fn exclude_plaintext_copies(root: &Path) -> Result<(), String> {
    const MARKER: &str = "# transcrypt-v3: editor and merge copies of *.secret files hold plaintext";
    let info = root.join(".git/info");
    if fs::symlink_metadata(&info).is_err() {
        fs::create_dir(&info).map_err(|e| format!("cannot create .git/info: {e}"))?;
    }
    let path = info.join("exclude");
    match fs::symlink_metadata(&path) {
        Ok(meta) if !meta.is_file() => return Err("unsafe .git/info/exclude".into()),
        _ => {},
    }
    let existing = fs::read_to_string(&path).unwrap_or_default();
    if existing.lines().any(|line| line == MARKER) { return Ok(()); }
    let mut block = String::new();
    if !existing.is_empty() && !existing.ends_with('\n') { block.push('\n'); }
    block.push_str(MARKER);
    block.push('\n');
    for pattern in ["*.secret~", "*.secret.sw[a-p]", "*.secret.orig", "*.secret.bak", "*.secret.tmp",
                    "*.secret.rej", "*.secret.save", "\\#*.secret#", ".#*.secret"] {
        block.push_str(pattern);
        block.push('\n');
    }
    fs::OpenOptions::new().append(true).create(true).open(&path)
        .and_then(|mut f| f.write_all(block.as_bytes()))
        .map_err(|e| format!("cannot update .git/info/exclude: {e}"))
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

/// The staged state that `verify_index` checked: the exact index listing
/// and its protected entries, all regular files.
struct Verified {
    listing: Vec<u8>,
    protected: Vec<Staged>,
}

/// Read one snapshot of the index and check it: the staged public metadata
/// equals the v3 policy and the worktree config, Git's effective filter
/// applies to every protected path, and every protected entry is a regular
/// file whose blob opens at its own path under the agent's key (`keyed`) or,
/// while locked, at least has the envelope of this configuration.
fn check_index(root: &Path, keyed: bool) -> Result<Verified, String> {
    let config = load_config(root)?;
    let listing = git(root, &["ls-files", "--stage", "-z"])?;
    let entries = parse_listing(&listing)?;
    let metadata = |name: &[u8], expected: &[u8], message: &str| -> Result<(), String> {
        match entries.iter().find(|e| e.path == name) {
            Some(e) if e.regular && git_blob(root, &e.oid)? == expected => Ok(()),
            _ => Err(message.into()),
        }
    };
    metadata(b".transcrypt/config", &config,
        "staged .transcrypt/config is missing, not a regular file or differs from the worktree")?;
    metadata(b".gitattributes", ATTRS, "staged .gitattributes differs from required v3 policy")?;
    if keyed {
        session::request(root, &config, Operation::Ping, &[], &[])?;
    }
    let protected: Vec<Staged> = entries.into_iter().filter(|e| protected_path(&e.path)).collect();
    if protected.iter().any(|e| !e.regular) {
        return Err("protected path is not a regular file in staged index".into());
    }
    let paths: Vec<&[u8]> = protected.iter().map(|e| e.path.as_slice()).collect();
    // Fail before any decryption if the effective Git filter changed.
    verify_staged_filter_attributes(root, &paths)?;
    let id = transcrypt_v3::config_id(&config);
    for staged in &protected {
        let record = git_blob(root, &staged.oid)?;
        if keyed {
            session::request(root, &config, Operation::Decrypt, &staged.path, &record)?;
        } else if !record_envelope_ok(&record, &id) {
            return Err(format!("staged {} is not v3 ciphertext for this repository",
                String::from_utf8_lossy(&staged.path)));
        }
    }
    Ok(Verified { listing, protected })
}

/// Full verification with the unlocked agent; required by hydrate and lock.
fn verify_index(root: &Path) -> Result<Verified, String> {
    check_index(root, true)
}

/// The pre-commit check. While locked the clean filter cannot run, so a
/// staged protected change can only come from bypassing it; the keyless
/// envelope check still rejects any plaintext, and committing unrelated
/// files keeps working.
fn verify_index_command(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    let unlocked = session::request(root, &config, Operation::Ping, &[], &[]).is_ok();
    check_index(root, unlocked)?;
    if !unlocked {
        eprintln!("transcrypt-v3: locked; checked staged record envelopes only");
    }
    Ok(())
}

/// Result of `audit`.
struct Audited {
    records: usize,
    authenticated: bool,
}

/// Check committed history: in every commit `git rev-list <revs>` names
/// (default `HEAD`), every `*.secret` entry must be a regular file whose blob
/// is a v3 record for the configuration committed in the same tree. This
/// needs no key, so it also runs in CI or a server-side hook. When the agent
/// is unlocked for that configuration, each record is also authenticated at
/// its path.
fn audit(root: &Path, revs: &[OsString], keyed: bool) -> Result<Audited, String> {
    let mut command = git_command(Some(root));
    command.arg("rev-list");
    if revs.is_empty() { command.arg("HEAD"); } else { command.args(revs); }
    let commits = output(command)?;
    // Per committed config blob: its bytes, id and whether the agent serves it.
    let mut configs: HashMap<String, (Vec<u8>, [u8; transcrypt_v3_core::ID_LEN], bool)> = HashMap::new();
    let mut checked: HashSet<(String, String, Vec<u8>)> = HashSet::new();
    let mut audited = Audited { records: 0, authenticated: true };
    for commit in commits.split(|b| *b == b'\n').filter(|c| !c.is_empty()) {
        if !is_object_id(commit) {
            return Err("unexpected git rev-list output".into());
        }
        let commit = String::from_utf8_lossy(commit).into_owned();
        let entries = tree_files(root, &commit)?;
        let at = |path: &[u8]| format!("commit {commit}, {}", String::from_utf8_lossy(path));
        if let Some(copy) = entries.iter().find(|e| plaintext_copy_name(&e.path)) {
            return Err(format!("{}: looks like an unencrypted editor or merge copy of a secret; \
                remove it from the commit", at(&copy.path)));
        }
        let protected: Vec<&Staged> = entries.iter().filter(|e| protected_path(&e.path)).collect();
        if protected.is_empty() { continue; }
        let Some(config_entry) = entries.iter().find(|e| e.path == b".transcrypt/config" && e.regular) else {
            return Err(format!("{}: *.secret file in a commit without a v3 configuration (plaintext?)",
                at(&protected[0].path)));
        };
        if !configs.contains_key(&config_entry.oid) {
            let bytes = git_blob(root, &config_entry.oid)?;
            transcrypt_v3_core::parse_config(&bytes)
                .map_err(|_| format!("commit {commit}: invalid v3 configuration"))?;
            let id = transcrypt_v3::config_id(&bytes);
            let live = keyed && session::request(root, &bytes, Operation::Ping, &[], &[]).is_ok();
            configs.insert(config_entry.oid.clone(), (bytes, id, live));
        }
        let (config, id, live) = &configs[&config_entry.oid];
        for entry in protected {
            if !entry.regular {
                return Err(format!("{}: protected path is not a regular file", at(&entry.path)));
            }
            if !checked.insert((entry.oid.clone(), config_entry.oid.clone(), entry.path.clone())) { continue; }
            let record = git_blob(root, &entry.oid).map_err(|e| format!("{}: {e}", at(&entry.path)))?;
            if !record_envelope_ok(&record, id) {
                return Err(format!("{}: not v3 ciphertext for its configuration (plaintext?)", at(&entry.path)));
            }
            if *live {
                session::request(root, config, Operation::Decrypt, &entry.path, &record)
                    .map_err(|e| format!("{}: {e}", at(&entry.path)))?;
            } else {
                audited.authenticated = false;
            }
            audited.records += 1;
        }
    }
    Ok(audited)
}

/// The pre-push hook: audit every commit being pushed that the remote does
/// not already have. Git supplies `<local ref> SP <local oid> SP <remote
/// ref> SP <remote oid>` lines on stdin.
fn pre_push(root: &Path, remote: Option<&OsStr>) -> Result<(), String> {
    // Never silently drop refs: oversized input is refused, not truncated.
    let input = read_limited(io::stdin(), MAX_RECORD).map_err(|_| "cannot read pre-push input")?;
    let mut revs: Vec<OsString> = Vec::new();
    for line in input.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
        let fields: Vec<&[u8]> = line.split(|b| *b == b' ').collect();
        if fields.len() != 4 || !is_object_id(fields[1]) || !is_object_id(fields[3]) {
            return Err("malformed pre-push input".into());
        }
        let zero = |oid: &[u8]| oid.iter().all(|b| *b == b'0');
        if zero(fields[1]) { continue; } // deleting a remote ref pushes nothing
        revs.push(OsString::from_vec(fields[1].to_vec()));
        let mut known = fields[3].to_vec();
        known.extend_from_slice(b"^{commit}");
        if !zero(fields[3]) && git(root, &["cat-file", "-e", &String::from_utf8_lossy(&known)]).is_ok() {
            let mut exclude = b"^".to_vec();
            exclude.extend_from_slice(fields[3]);
            revs.push(OsString::from_vec(exclude));
        }
    }
    if revs.is_empty() { return Ok(()); }
    // Commits on this remote's tracking branches were audited when pushed.
    // Only a plain remote name is used as a pattern; anything else (a URL)
    // audits the complete history being pushed.
    if let Some(name) = remote.and_then(OsStr::to_str) {
        if !name.is_empty() && name.bytes().all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b)) {
            revs.push("--not".into());
            revs.push(format!("--remotes={name}").into());
        }
    }
    audit(root, &revs, true).map(|_| ())
        .map_err(|e| format!("{e}\nrefusing to push; see `transcrypt-v3 audit`"))
}

/// Private staging directory for whole-file replacements:
/// `.git/transcrypt-v3-staging`, a real mode-0700 directory held open by fd.
/// Temporaries never live in the worktree, so a crash cannot leave plaintext
/// where `git add` could commit it unencrypted, and Git never reads files
/// under `.git`. Holding it also holds an exclusive lock, so worktree-
/// mutating operations (`hydrate`, `lock`) never interleave, and anything
/// left in it is from an interrupted earlier run and is removed.
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
    dir.try_lock().map_err(|_| "another transcrypt-v3 hydrate or lock is running in this repository")?;
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
    let staging = staging_dir(root)?;
    let config = load_config(root)?;
    // Authenticate ALL staged protected objects and the staged metadata
    // before exposing any plaintext in the checkout. Everything below uses
    // the object ids of this verified snapshot.
    let verified = verify_index(root)?;
    let mut pending = Vec::new();
    let mut kept = Vec::new();

    // Validate the complete worktree first. A checkout may contain a mixture
    // of ciphertext and already-hydrated plaintext after an interrupted run.
    // Neither an unexpected third value nor a protected symlink is replaced.
    for staged in &verified.protected {
        let object = git_blob(root, &staged.oid)?;
        let plaintext = session::request(root, &config, Operation::Decrypt, &staged.path, &object)?;
        let relative = indexed_path(&staged.path)?;
        let (worktree, stamp) = open_protected(root, &relative)?.read()?;
        match hydrate_action(&worktree, &object, &plaintext) {
            Ok(HydrateAction::Publish) => pending.push((staged, relative, stamp)),
            Ok(HydrateAction::Keep) => kept.push(relative),
            Err(_) => return Err("protected worktree differs from staged ciphertext and authenticated plaintext; refusing overwrite".into()),
        }
    }
    // Detect a changed index or public configuration between validation and
    // publication.
    if git(root, &["ls-files", "--stage", "-z"])? != verified.listing || load_config(root)? != config {
        return Err("index or public configuration changed during hydration".into());
    }

    for (i, (staged, relative, stamp)) in pending.into_iter().enumerate() {
        // Same object id, hence the same bytes that were authenticated above.
        let object = git_blob(root, &staged.oid)?;
        let plaintext = session::request(root, &config, Operation::Decrypt, &staged.path, &object)?;
        // `replace` refuses unless the file is still the ciphertext checked above.
        open_protected(root, &relative)?.replace(&staging, &plaintext, i, &stamp)?;
    }
    // Plaintext that Git's checkout (smudge) wrote follows the umask and may
    // be readable by other users; published files are already 0600.
    for relative in &kept {
        open_protected(root, relative)?.make_private()?;
    }
    // Git's index still caches the size/mtime of the encrypted checkout, and
    // `update-index --refresh` skips files whose size changed. Re-index
    // exactly the protected paths through the clean filter instead:
    // `update-index -z --stdin` takes raw path bytes, never pathspecs (a
    // tracked `[a].secret` must not select an untracked `a.secret`), and
    // without `--add` cannot stage an untracked file. `reindex` verifies that
    // no staged blob or mode changed, even when index != HEAD.
    reindex(root, &verified)?;
    eprintln!("Hydration complete.");
    Ok(())
}

/// Re-index exactly the verified protected paths through the clean filter
/// and check that no staged blob or mode changed.
fn reindex(root: &Path, verified: &Verified) -> Result<(), String> {
    let mut paths = Vec::new();
    for staged in &verified.protected {
        paths.extend_from_slice(&staged.path);
        paths.push(0);
    }
    git_with_input(root, &["update-index", "-z", "--stdin"], &paths)?;
    if git(root, &["ls-files", "--stage", "-z"])? != verified.listing {
        return Err("staged Git objects changed while refreshing the index; inspect `git diff --cached`".into());
    }
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
        // A concurrent operation cannot enter (or purge) while it is held.
        assert!(staging_dir(&tmp).is_err());
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        let path = tmp.join("item.secret");
        fs::write(&path, b"ciphertext placeholder").unwrap();
        let target = open_protected(&tmp, Path::new("item.secret")).unwrap();
        let (_, stamp) = target.read().unwrap();
        target.replace(&staging, b"authenticated plaintext", 0, &stamp).unwrap();
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
    fn replacement_refuses_a_file_changed_since_it_was_checked() {
        let tmp = std::env::temp_dir().join(format!(
            "transcrypt-v3-stamp-{}", std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(tmp.join(".git")).unwrap();
        let staging = staging_dir(&tmp).unwrap();
        let path = tmp.join("item.secret");
        fs::write(&path, b"checked contents").unwrap();
        let target = open_protected(&tmp, Path::new("item.secret")).unwrap();
        let (_, stamp) = target.read().unwrap();
        // A concurrent edit after the check, even one of the same size.
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(&path, b"edited contents!").unwrap();
        assert!(target.replace(&staging, b"replacement", 0, &stamp).is_err());
        assert_eq!(fs::read(&path).unwrap(), b"edited contents!", "edit must survive");
        // So is a file replaced by a different inode.
        let (_, stamp) = target.read().unwrap();
        fs::remove_file(&path).unwrap();
        fs::write(&path, b"edited contents!").unwrap();
        assert!(target.replace(&staging, b"replacement", 1, &stamp).is_err());
        assert_eq!(fs::read_dir(tmp.join(".git/transcrypt-v3-staging")).unwrap().count(), 0);
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
        let (contents, stamp) = target.read().unwrap();
        assert_eq!(*contents, b"test");
        // Race: after resolution, the parent is swapped for a symlink to an
        // outside directory. The held directory fd keeps the write inside.
        let staging = staging_dir(&checkout).unwrap();
        fs::rename(checkout.join("regular"), checkout.join("moved")).unwrap();
        symlink(&external, checkout.join("regular")).unwrap();
        target.replace(&staging, b"plaintext", 0, &stamp).unwrap();
        assert_eq!(fs::read(external.join("item.secret")).unwrap(), b"test", "write escaped");
        assert_eq!(fs::read(checkout.join("moved/item.secret")).unwrap(), b"plaintext");
        let _ = fs::remove_dir_all(tmp);
    }
}
