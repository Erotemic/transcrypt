//! The `transcrypt-v3` command: the effectful adapter around the verified
//! core (`transcrypt-v3-core`), outside the Aeneas proof boundary.
//!
//! - `main.rs`: command dispatch, the Git filters, `verify-index`, `hydrate`,
//!   `lock` and `status`, the lifecycle steps whose order the Lean models
//!   follow.
//! - `git.rs`: every Git subprocess (bounded), object reads by verified id,
//!   listings parsed by the verified core.
//! - `worktree.rs`: race-free protected-file access and private staging.
//! - `setup.rs`: init, unlock, filters, hooks, ignore rules, `doctor`.
//! - `audit.rs`: keyless history audit and the pre-push hook.
//! - `process.rs`: Git's long-running filter protocol (one filter process
//!   per Git command); `merge.rs` and `diff.rs`: the merge and diff drivers
//!   for protected files.
//! - `session.rs`: the in-memory credential agent; `fsat.rs`: dirfd I/O.
#[cfg(not(unix))]
compile_error!("transcrypt-v3 POC requires Unix for 0600/0700 local credential permissions");

use std::{
    env, fs,
    ffi::OsString,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::ExitCode,
};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;
use zeroize::Zeroizing;
mod audit;
mod diff;
mod fsat;
mod git;
mod merge;
mod process;
mod session;
mod setup;
mod worktree;
use session::Operation;
use transcrypt_v3_core::{
    hydrate_action, lock_action, record_envelope_ok,
    HydrateAction, LockAction, MAX_RECORD,
};
use audit::*;
use git::*;
use setup::*;
use worktree::*;

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
        let mut revs = &args[1..];
        let mut max_commits = None;
        if let Some(limit) = revs.first().and_then(|a| a.to_str()).and_then(|a| a.strip_prefix("--max-commits=")) {
            max_commits = Some(limit.parse::<usize>().map_err(|_| "--max-commits takes a number")?);
            revs = &revs[1..];
        }
        let audited = audit(&root, revs, keyed, max_commits)?;
        println!("audit: {} protected record(s) checked{}", audited.records,
            if audited.authenticated { ", all authenticated by the unlocked agent" }
            else { " (envelopes only: unlock to authenticate them)" });
        return Ok(());
    }
    let root = repo_root()?;
    // File arguments (the merge driver's) are relative to where Git ran us.
    let invoked_in = env::current_dir().map_err(|_| "cannot read working directory")?;
    // All v3 paths, including the agent's short relative socket address,
    // are interpreted from the repository root.
    env::set_current_dir(&root).map_err(|_| "cannot enter repository root")?;
    match action {
        "status" => {
            if args.len() != 1 { return Err("status takes no arguments".into()); }
            status(&root)
        },
        "doctor" => {
            if args.len() != 1 { return Err("doctor takes no arguments".into()); }
            doctor(&root)
        },
        "init" | "unlock" | "rekey" => {
            let mut stdin = false;
            let mut auto_hydrate = true;
            for arg in &args[1..] {
                match arg.to_str() {
                    Some("--password-stdin") if !stdin => stdin = true,
                    Some("--no-hydrate") if action == "unlock" && auto_hydrate => auto_hydrate = false,
                    _ => return Err("init and rekey accept --password-stdin; unlock accepts --password-stdin and --no-hydrate".into()),
                }
            }
            let password = passphrase(stdin, action != "unlock")?;
            match action {
                "init" => init(&root, password),
                "rekey" => rekey(&root, password),
                _ => unlock(&root, password, auto_hydrate),
            }
        },
        "diff" => {
            // Git's external diff interface: path old-file old-hex old-mode
            // new-file new-hex new-mode [new-path rename-message].
            let file = |arg: &OsString| invoked_in.join(arg);
            match &args[1..] {
                [path, old, _, _, new, _, _] => diff::diff(&root, path.as_bytes(), &file(old), path.as_bytes(), &file(new)),
                [path, old, _, _, new, _, _, new_path, _] =>
                    diff::diff(&root, path.as_bytes(), &file(old), new_path.as_bytes(), &file(new)),
                [path] => { println!("* Unmerged path {}", path.to_string_lossy()); Ok(()) },
                _ => Err("unexpected external diff arguments".into()),
            }
        },
        "merge" => {
            let [_, base, ours, theirs, path] = &args[..] else {
                return Err("merge driver takes %O %A %B %P".into());
            };
            let file = |arg: &OsString| invoked_in.join(arg);
            if merge::merge(&root, &file(base), &file(ours), &file(theirs), path.as_bytes())? {
                Ok(())
            } else {
                Err(format!("merge conflict in {}: resolve it in the decrypted file", path.to_string_lossy()))
            }
        },
        "filter-process" => {
            if args.len() != 1 { return Err("filter-process takes no arguments".into()); }
            process::serve(&root)
        },
        "clean" | "smudge" => {
            if args.len() != 2 { return Err("Git filter requires exactly one %f pathname".into()); }
            filter(&root, action == "clean", args[1].as_bytes())
        },
        "pre-push" => {
            if args.len() > 3 { return Err("pre-push takes the remote name and URL".into()); }
            pre_push(&root, args.get(1).map(OsString::as_os_str))
        },
        "hydrate" if args.len() == 2 && args[1] == "--auto" => auto_hydrate(&root),
        "lock" | "verify-index" | "hydrate" | "serve" | "uninstall" => {
            if args.len() != 1 { return Err("unexpected operation arguments".into()); }
            match action {
                "lock" => lock(&root),
                "verify-index" => verify_index_command(&root),
                "hydrate" => hydrate(&root).map(|n| eprintln!("Hydration complete: {n} file(s) decrypted.")),
                "serve" => session::serve(&root, &load_config(&root)?),
                "uninstall" => uninstall(&root),
                _ => unreachable!(),
            }
        },
        _ => Err(format!("unknown v3 operation; {USAGE}")),
    }
}

const USAGE: &str = "usage: transcrypt-v3 init|unlock|hydrate|status|doctor|verify-index|audit|lock|rekey|uninstall|help \
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
  transcrypt-v3 doctor      verify that filters, attributes, hooks and the staged index
                            protect this checkout (non-zero exit if anything is missing)
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
  transcrypt-v3 rekey       change the passphrase: a new config and every *.secret re-encrypted,
                            staged for you to commit (old commits keep the old passphrase)
  transcrypt-v3 uninstall   lock, then remove the filters, hooks and ignore rules from this
                            checkout (committed files and history stay encrypted)

Options
  --password-stdin          (init, unlock, rekey) read the passphrase from stdin instead of the
                            terminal (where a new passphrase is asked for twice)
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
    let index = index_with_conflicts(root)?;
    for path in index.conflicted.iter().filter(|p| protected_path(p)) {
        let decrypted = find_protected(root, &indexed_path(path)?).ok().flatten()
            .and_then(|t| t.read().ok())
            .is_some_and(|(bytes, _)| !record_envelope_ok(&bytes, &transcrypt_v3::config_id(&config)));
        counts[2] += 1;
        println!("  {:<22} {}", if decrypted { "conflicted" } else { "conflicted (encrypted)" },
            String::from_utf8_lossy(path));
    }
    for staged in index.merged {
        if !protected_path(&staged.path) { continue; }
        let name = String::from_utf8_lossy(&staged.path).into_owned();
        let state = (|| -> Result<&str, String> {
            if !staged.regular { return Ok("unsupported mode"); }
            let object = git_blob(root, &staged.oid)?;
            let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? else {
                return Ok("deleted");
            };
            let (worktree, _) = target.read()?;
            if *worktree == object { return Ok("ciphertext"); }
            if target.readable_by_others()? { exposed += 1; }
            if !unlocked { return Ok("modified or plaintext"); }
            let plaintext = session::request(root, &config, Operation::Decrypt, &staged.path, &object)?;
            Ok(if *worktree == *plaintext { "plaintext" } else { "modified" })
        })().unwrap_or("error");
        counts[match state { "ciphertext" => 0, "plaintext" => 1, "modified" | "modified or plaintext" | "deleted" => 2, _ => 3 }] += 1;
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

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
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

/// Read the passphrase. A new one (`init`, `rekey`) typed on a terminal is
/// asked for twice: a typo would otherwise encrypt everything under a
/// passphrase nobody knows.
fn passphrase(from_stdin: bool, new: bool) -> Result<Zeroizing<Vec<u8>>, String> {
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
        let prompt = |text: &str| rpassword::prompt_password(text)
            .map(|p| Zeroizing::new(p.into_bytes()))
            .map_err(|e| format!("cannot read terminal passphrase: {e}"));
        let value = prompt(if new { "New transcrypt v3 passphrase: " } else { "Transcrypt v3 passphrase: " })?;
        if new && value.len() >= 16 && *prompt("Repeat the passphrase: ")? != *value {
            return Err("the passphrases differ".into());
        }
        value
    };
    if bytes.len() < 16 { return Err("v3 requires a passphrase of at least 16 bytes".into()); }
    Ok(bytes)
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
    let mut present = Vec::new();
    for staged in &verified.protected {
        let relative = indexed_path(&staged.path)?;
        // A deleted file holds no plaintext: nothing to flush.
        let Some(target) = find_protected(root, &relative)? else { continue };
        present.push(staged.path.clone());
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
    reindex(root, &verified.listing, &present)?;
    session::stop(root, &config)?;
    eprintln!("Locked: tracked *.secret files flushed and the in-memory credential agent stopped. This does not securely erase historical plaintext backups.");
    Ok(())
}

/// The per-file Git filter (`clean %f` / `smudge %f`): stdin to stdout.
fn filter(root: &Path, clean: bool, git_path: &[u8]) -> Result<(), String> {
    let input = Zeroizing::new(read_limited(io::stdin(), MAX_RECORD)?);
    let output = convert(root, clean, git_path, input)?;
    io::stdout().write_all(&output).map_err(|_| "cannot write output")?;
    Ok(())
}

/// One clean or smudge conversion of the file at `git_path`, shared by the
/// per-file filters and the long-running `filter-process`.
fn convert(root: &Path, clean: bool, git_path: &[u8], input: Zeroizing<Vec<u8>>)
    -> Result<Zeroizing<Vec<u8>>, String>
{
    transcrypt_v3::validate_protected_path(git_path)?;
    let config = load_config(root)?;
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
        return Ok(input);
    }
    // The agent's clean returns a record that already opens at this path
    // unchanged and otherwise seals with the verified core's `seal_record`,
    // which refuses any other v3 record (double encryption); `open_record`
    // releases plaintext only after authenticating it under this config and
    // exact Git path.
    if clean {
        return session::request(root, &config, Operation::Encrypt, git_path, &input);
    }
    let plaintext = session::request(root, &config, Operation::Decrypt, git_path, &input)?;
    if !umask_is_private() {
        // Git would create this file readable by other users. Emit the
        // record, now authenticated, unchanged; the post-checkout hook (or
        // `hydrate`) publishes the plaintext with mode 0600.
        return Ok(input);
    }
    Ok(plaintext)
}

/// Whether files Git creates now are private to this user. Git creates
/// worktree files with mode `0666 & !umask`, and its filters inherit its
/// umask, so the smudge filter sees exactly the mask Git will apply.
fn umask_is_private() -> bool {
    // SAFETY: umask cannot fail; this process is single-threaded here and
    // restores the previous mask immediately.
    let previous = unsafe { libc::umask(0o077) };
    unsafe { libc::umask(previous) };
    previous & 0o077 == 0o077
}

fn protected_path(path: &[u8]) -> bool {
    transcrypt_v3_core::is_protected_path(path)
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
    if let Some(copy) = entries.iter().find(|e| plaintext_copy_name(&e.path)) {
        return Err(format!("staged {} looks like an unencrypted editor or merge copy of a secret; \
            unstage it", String::from_utf8_lossy(&copy.path)));
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

/// Run from the post-checkout, post-merge and post-rewrite hooks: hydrate
/// if unlocked, and never fail the Git command that already finished.
fn auto_hydrate(root: &Path) -> Result<(), String> {
    let Ok(config) = load_config(root) else { return Ok(()) };
    if session::request(root, &config, Operation::Ping, &[], &[]).is_err() {
        return Ok(());
    }
    match hydrate(root) {
        Ok(0) => {},
        Ok(n) => eprintln!("transcrypt-v3: decrypted {n} file(s) with mode 0600."),
        Err(e) => eprintln!("transcrypt-v3: automatic hydration skipped: {e}\n\
            Inspect with `transcrypt-v3 status`, then run `transcrypt-v3 hydrate`."),
    }
    Ok(())
}

/// Decrypt, with mode 0600, every protected worktree file that is an
/// authentic record for its own path: the staged ciphertext of a fresh
/// checkout, or another genuine record that Git wrote (a restored or
/// stash-popped version). Every other file (plaintext, edited or not) is
/// left as it is, only made private. Nothing but an authentic record is ever
/// replaced, so no edit can be lost, and replacing a record by its plaintext
/// loses nothing (clean seals it back to the same record).
fn hydrate(root: &Path) -> Result<usize, String> {
    hydrate_locked(root, &staging_dir(root)?)
}

/// `hydrate` for a caller that already holds the staging lock.
fn hydrate_locked(root: &Path, staging: &Staging) -> Result<usize, String> {
    let config = load_config(root)?;
    let index = index_with_conflicts(root)?;
    let conflicted: Vec<&[u8]> = index.conflicted.iter().map(Vec::as_slice).filter(|p| protected_path(p)).collect();
    let protected: Vec<&Staged> = if conflicted.is_empty() {
        // Authenticate ALL staged protected objects, the staged metadata and
        // the effective filter before exposing any plaintext in the checkout.
        let verified = verify_index(root)?;
        if verified.listing != index.listing {
            return Err("index changed during hydration".into());
        }
        index.merged.iter().filter(|e| protected_path(&e.path)).collect()
    } else {
        // A merge is in progress: the stages of an unmerged path are the
        // merge's inputs, not a snapshot to verify. Still require the agent
        // and the effective filter for every protected path, so plaintext
        // published here is encrypted again by `git add`.
        session::request(root, &config, Operation::Ping, &[], &[])?;
        let protected: Vec<&Staged> = index.merged.iter().filter(|e| protected_path(&e.path)).collect();
        if protected.iter().any(|e| !e.regular) {
            return Err("protected path is not a regular file in staged index".into());
        }
        let paths: Vec<&[u8]> = protected.iter().map(|e| e.path.as_slice()).chain(conflicted.iter().copied()).collect();
        verify_staged_filter_attributes(root, &paths)?;
        protected
    };
    let id = transcrypt_v3::config_id(&config);
    let mut pending = Vec::new();
    let mut refresh = Vec::new();
    let mut kept = Vec::new();

    // Decide for every file before writing any. A protected symlink or
    // unreadable file aborts the whole operation. Unmerged files have no
    // staged record of their own; they are decrypted when they hold a
    // record that authenticates at their path (the merge driver's result).
    let targets = protected.iter().map(|e| (e.path.as_slice(), Some(e.oid.as_str())))
        .chain(conflicted.iter().map(|p| (*p, None)));
    for (path, oid) in targets {
        let relative = indexed_path(path)?;
        // A deleted (or sparse) file holds nothing to decrypt.
        let Some(target) = find_protected(root, &relative)? else { continue };
        let (worktree, stamp) = target.read()?;
        let object = match oid { Some(oid) => git_blob(root, oid)?, None => Vec::new() };
        // The record this file holds, if any: the staged one, or another
        // that authenticates at this path.
        let is_staged = oid.is_some() && *worktree == object;
        let record: Option<&[u8]> = if is_staged {
            Some(&object)
        } else if record_envelope_ok(&worktree, &id) {
            Some(&worktree)
        } else {
            None
        };
        if let Some(record) = record {
            let plaintext = session::request(root, &config, Operation::Decrypt, path, record)
                .map_err(|e| format!("{}: {e}", String::from_utf8_lossy(path)))?;
            if hydrate_action(&worktree, record, &plaintext) == Ok(HydrateAction::Publish) {
                pending.push((path, relative, stamp, record.to_vec(), is_staged));
                continue;
            }
        }
        if oid.is_some() {
            let plaintext = session::request(root, &config, Operation::Decrypt, path, &object)?;
            if hydrate_action(&worktree, &object, &plaintext) == Ok(HydrateAction::Keep) {
                refresh.push(path.to_vec());
            }
        }
        kept.push(relative);
    }
    // Detect a changed index or public configuration between validation and
    // publication.
    if git(root, &["ls-files", "--stage", "-z"])? != index.listing || load_config(root)? != config {
        return Err("index or public configuration changed during hydration".into());
    }
    let published = pending.len();
    for (i, (path, relative, stamp, record, is_staged)) in pending.into_iter().enumerate() {
        let plaintext = session::request(root, &config, Operation::Decrypt, path, &record)?;
        // `replace` refuses unless the file is still the record checked above.
        open_protected(root, &relative)?.replace(staging, &plaintext, i, &stamp)?;
        if is_staged { refresh.push(path.to_vec()); }
    }
    // Plaintext that Git's checkout wrote follows the umask and may be
    // readable by other users; published files are already 0600.
    for relative in &kept {
        open_protected(root, relative)?.make_private()?;
    }
    // Git's index still caches the size/mtime of the encrypted checkout, and
    // `update-index --refresh` skips files whose size changed. Re-index the
    // files that now hold exactly the staged plaintext (never an edit or a
    // different version, which would stage it) through the clean filter:
    // `update-index -z --stdin` takes raw path bytes, never pathspecs (a
    // tracked `[a].secret` must not select an untracked `a.secret`), and
    // without `--add` cannot stage an untracked file. `reindex` verifies that
    // no staged blob or mode changed, even when index != HEAD.
    reindex(root, &index.listing, &refresh)?;
    Ok(published)
}
