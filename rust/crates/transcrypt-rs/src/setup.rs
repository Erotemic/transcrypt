//! Installing v3 in a checkout: init, unlock and uninstall, the Git
//! filters, drivers and hooks, and the two read-only reports, `status` and
//! `doctor` (which checks that all of them are in place).

use std::{
    env,
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
};
use zeroize::Zeroizing;
use transcrypt_rs::{initialize_config, unlock_config, SecretKey};
use transcrypt_v3_core::{parse_file_header, record_envelope_ok, ATTRIBUTES_NAME, SALT_LEN};
use crate::{
    attributes::{edit_attributes, filter_overrides, protect, restore_worktree_attributes, worktree_attributes},
    credential::{self, Key, Unlock},
    git::*,
    short_id,
    lifecycle::*,
    load_config, os, passphrase, session,
    worktree::{find_protected, indexed_path, staging_dir, write_repository_file},
    Options,
};

const HOOKS_BYPASSED: &str = "core.hooksPath is set, so Git does not run the v3 pre-commit and \
    pre-push checks installed in .git/hooks";

/// How to discard an interrupted `init`, for its refusals.
const START_OVER: &str = "`git rm -q -r --cached --ignore-unmatch .transcrypt; rm -r .transcrypt`";

/// Where Git runs hooks from by default, and v3 installs its own.
fn hooks_dir(root: &Path) -> PathBuf {
    common_dir(root).join("hooks")
}

/// Whether Git is configured to run hooks from somewhere other than
/// `.git/hooks`, where v3 installs its checks.
fn hooks_bypassed(root: &Path) -> bool {
    let Ok(value) = git(root, &["config", "--path", "core.hooksPath"]) else { return false };
    let value = String::from_utf8_lossy(&value).trim().to_owned();
    if value.is_empty() { return false; }
    let configured = root.join(&value);
    configured.canonicalize().ok() != hooks_dir(root).canonicalize().ok()
}

fn shell_quote(text: &str) -> String {
    format!("'{}'", text.replace('\'', "'\\''"))
}

fn program() -> Result<String, String> {
    let bin = env::current_exe().map_err(|_| "cannot resolve current executable")?;
    Ok(shell_quote(bin.to_str().ok_or("executable path must be UTF-8")?))
}

/// The Git filter, merge and diff driver configuration this binary installs.
fn expected_config() -> Result<[(&'static str, String); 7], String> {
    let program = program()?;
    Ok([
        // Required first: an interrupted install then fails Git's commands
        // rather than letting them store plaintext.
        ("filter.transcrypt-v3.required", "true".into()),
        ("filter.transcrypt-v3.clean", format!("{program} clean %f")),
        ("filter.transcrypt-v3.smudge", format!("{program} smudge %f")),
        // Preferred by Git when present: one process per Git command.
        ("filter.transcrypt-v3.process", format!("{program} filter-process")),
        ("merge.transcrypt-v3.name", "transcrypt-rs: merge decrypted protected files".into()),
        ("merge.transcrypt-v3.driver", format!("{program} merge %O %A %B %P")),
        ("diff.transcrypt-v3.command", format!("{program} diff")),
    ])
}

/// The local attribute line that older versions wrote to
/// `.git/info/attributes`; the macro replaces it.
const LEGACY_MERGE_ATTRIBUTE: &str = "*.secret diff=transcrypt-v3 merge=transcrypt-v3";

fn install_filters(root: &Path) -> Result<(), String> {
    for (k, value) in expected_config()? {
        git(root, &["config", "--local", k, &value])?;
    }
    Ok(())
}

/// The filters and drivers, then the hooks.
fn install(root: &Path) -> Result<(), String> {
    install_filters(root)?;
    install_hooks(root)
}

fn remove_filters(root: &Path) {
    for section in ["filter.transcrypt-v3", "merge.transcrypt-v3", "diff.transcrypt-v3"] {
        let _ = git(root, &["config", "--local", "--remove-section", section]);
    }
}

/// Hooks installed by init and unlock, with the v3 command each runs: seal
/// and verify the staged index before every commit, and audit the commits
/// being pushed (which also covers merges, rebases and `--no-verify`
/// commits that never ran the pre-commit hook). The post-* hooks only serve
/// the private mode (decrypting after Git wrote ciphertext).
const HOOKS: [(&str, &str); 6] = [
    ("pre-commit", "pre-commit"),
    ("pre-push", "pre-push \"$@\""),
    // A merge that needs no conflict resolution commits without running
    // pre-commit. Its index holds the other side's content, which must only
    // be checked: the read-only `verify-index`, never the repairing hook.
    ("pre-merge-commit", "verify-index"),
    ("post-checkout", "hydrate --auto"),
    ("post-merge", "hydrate --auto"),
    ("post-rewrite", "hydrate --auto"),
];

/// The checks whose absence would let plaintext through. A foreign hook of
/// another name is left alone.
fn hook_required(name: &str) -> bool {
    matches!(name, "pre-commit" | "pre-push")
}

fn hook_script(command: &str) -> Result<String, String> {
    Ok(format!("#!/bin/sh\nexec {} {command}\n", program()?))
}

/// Whether `text` is a hook that some v3 binary installed, at whatever path
/// it was then (the binary may since have moved or been upgraded; `unlock`
/// then rewrites it for this binary).
fn ours(name: &str, command: &str, text: &str) -> bool {
    let legacy = if name == "pre-commit" { Some("verify-index") } else { None };
    let Some(line) = text.strip_prefix("#!/bin/sh\nexec ").and_then(|t| t.strip_suffix('\n')) else { return false };
    let Some((path, rest)) = shell_unquote(line) else { return false };
    // The exact form v3 writes, for a binary named transcrypt-rs or (before
    // the rename) transcrypt-v3; on Windows also with `.exe`, in any case.
    Path::new(&path).file_name().and_then(|n| n.to_str()).is_some_and(|name| {
        ["transcrypt-rs", "transcrypt-v3"].iter().any(|ours| if cfg!(windows) {
            name.eq_ignore_ascii_case(ours) || name.eq_ignore_ascii_case(&format!("{ours}.exe"))
        } else {
            name == *ours
        })
    })
        && [Some(command), legacy].into_iter().flatten()
            .any(|c| rest == c && line == format!("{} {c}", shell_quote(&path)))
}

/// Split `'quoted' rest` as `shell_quote` writes it (`'` inside as `'\''`).
fn shell_unquote(line: &str) -> Option<(String, &str)> {
    let mut path = String::new();
    let mut rest = line.strip_prefix('\'')?;
    loop {
        let end = rest.find('\'')?;
        path.push_str(&rest[..end]);
        rest = &rest[end + 1..];
        match rest.strip_prefix("\\''") {
            Some(more) => { path.push('\''); rest = more; },
            None => return Some((path, rest.strip_prefix(' ')?)),
        }
    }
}

fn hook_path(root: &Path, name: &str) -> PathBuf {
    hooks_dir(root).join(name)
}

fn check_hook_available(root: &Path) -> Result<(), String> {
    for (name, command) in HOOKS.into_iter().filter(|(name, _)| hook_required(name)) {
        let path = hook_path(root, name);
        match fs::symlink_metadata(&path) {
            Ok(meta) => {
                let text = fs::read_to_string(&path).map_err(|_| format!("cannot read existing {name} hook"))?;
                if !meta.is_file() || meta.file_type().is_symlink() || !ours(name, command, &text) {
                    return Err(format!("{name} hook already exists and is not the v3 hook; refusing to override it"));
                }
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(_) => return Err("cannot inspect hook directory".into()),
        }
    }
    Ok(())
}

fn install_hooks(root: &Path) -> Result<(), String> {
    check_hook_available(root)?;
    fs::create_dir_all(hooks_dir(root)).map_err(|e| format!("cannot create .git/hooks: {e}"))?;
    for (name, command) in HOOKS {
        let path = hook_path(root, name);
        let script = hook_script(command)?;
        if let Ok(text) = fs::read_to_string(&path) {
            if text == script {
                os::make_runnable(&path)
                    .map_err(|e| format!("cannot make the {name} hook executable: {e}"))?;
                continue;
            }
            if !ours(name, command, &text) { continue; }
            fs::remove_file(&path).map_err(|e| format!("cannot replace the {name} hook: {e}"))?;
        } else if fs::symlink_metadata(&path).is_ok() {
            continue;
        }
        os::create_hook(&path).map_err(|e| format!("cannot install {name} hook: {e}"))?
            .write_all(script.as_bytes()).map_err(|e| format!("cannot write {name} hook: {e}"))?;
    }
    if hooks_bypassed(root) {
        eprintln!("warning: {HOOKS_BYPASSED}");
    }
    Ok(())
}

fn remove_hooks(root: &Path) -> Result<(), String> {
    for (name, command) in HOOKS {
        remove_hook(root, name, command).map_err(|e| format!("cannot remove {name} hook: {e}"))?;
    }
    Ok(())
}

/// Remove the hook `name` if it is one that v3 installed.
fn remove_hook(root: &Path, name: &str, command: &str) -> io::Result<()> {
    let path = hook_path(root, name);
    if fs::read_to_string(&path).is_ok_and(|text| ours(name, command, &text)) { fs::remove_file(&path)?; }
    Ok(())
}

/// Make `key` the credential of this checkout, in the requested mode, and
/// remove the other mode's.
pub(crate) fn activate(root: &Path, config: &[u8], key: &SecretKey, private: bool, idle: Option<std::time::Duration>)
    -> Result<(), String>
{
    if private {
        credential::forget(root)?;
        if Key::load(root, config)?.is_none() {
            session::start(root, config, key, idle)?;
        }
    } else {
        credential::store(root, config, key)?;
        let _ = session::stop(root, config);
    }
    Ok(())
}

/// `init [PATTERN...]`: a new config and key, the attribute macro in
/// `.gitattributes`, filters and hooks, the key stored (or the private
/// agent started), and then `protect` for each pattern.
pub(crate) fn init(root: &Path, options: &Options) -> Result<(), String> {
    let rollback = init_with_rollback(root, options, None)?;
    if !options.patterns.is_empty() {
        if let Err(e) = protect(root, &options.patterns) {
            rollback.run();
            return Err(format!("{e}; initialization rolled back"));
        }
    } else {
        eprintln!("Choose what to encrypt, for example:\n  transcrypt-rs protect .env 'secrets/**'");
    }
    eprintln!("Then commit:\n  git commit -m 'Enable transcrypt-v3'");
    Ok(())
}

/// What a successful initialization created, so that a later failure of
/// the same command (`protect`, `migrate`) can undo it and the command can
/// simply be rerun.
pub(crate) struct Rollback {
    root: PathBuf,
    config: Vec<u8>,
    attributes_before: Option<Vec<u8>>,
    hook_preexisted: [bool; HOOKS.len()],
}

impl Rollback {
    /// Undo exactly what initialization created: staged metadata, the files
    /// it wrote (the config only if unchanged), its hooks (only those that
    /// did not exist before), its Git configuration and the key.
    pub(crate) fn run(&self) {
        let root = self.root.as_path();
        let _ = git(root, &["reset", "-q", "--", CONFIG_PATH, ".gitattributes"]);
        if fs::read(root.join(CONFIG_PATH)).ok().as_deref() == Some(&self.config[..]) {
            let _ = fs::remove_file(root.join(CONFIG_PATH));
            let _ = fs::remove_dir(root.join(".transcrypt"));
        }
        restore_worktree_attributes(root, self.attributes_before.as_deref());
        for ((name, command), preexisted) in HOOKS.into_iter().zip(self.hook_preexisted) {
            if !preexisted { let _ = remove_hook(root, name, command); }
        }
        remove_filters(root);
        let _ = credential::forget(root);
        let _ = session::stop(root, &self.config);
    }
}

/// A fresh salt and the config and key it gives with `password`.
pub(crate) fn new_config(password: &[u8]) -> Result<([u8; transcrypt_v3_core::CONFIG_LEN], SecretKey), String> {
    let mut salt = [0u8; SALT_LEN];
    getrandom::fill(&mut salt).map_err(|_| "OS randomness unavailable")?;
    initialize_config(password, &salt)
}

/// Whether `.transcrypt` exists but `HEAD` has no config: an interrupted
/// `init` or `migrate`, which rerunning completes. `committed` is the
/// refusal when `HEAD` already has one.
pub(crate) fn uncommitted_setup(root: &Path, committed: &str) -> Result<bool, String> {
    if fs::symlink_metadata(root.join(".transcrypt")).is_err() { return Ok(false); }
    if config_blob(root, "HEAD").ok().flatten().is_some() { return Err(committed.into()); }
    Ok(true)
}

/// Initialize (without protecting anything yet); on failure everything is
/// rolled back, on success the caller gets the rollback for later steps.
pub(crate) fn init_with_rollback(root: &Path, options: &Options, password: Option<Zeroizing<Vec<u8>>>)
    -> Result<Rollback, String>
{
    // An existing config not yet in `HEAD` is an interrupted `init`: rerunning
    // with the same passphrase completes it.
    let committed = ".transcrypt already exists: this repository is set up; run `transcrypt-rs unlock`";
    let interrupted = if uncommitted_setup(root, committed)? {
        Some(load_config(root).map_err(|e| format!("{e} (left by an interrupted init? to start over: {START_OVER})"))?)
    } else { None };
    check_hook_available(root)?;
    // Asked before anything is written: an interrupted prompt changes nothing.
    let password = match password { Some(p) => p, None => passphrase(options.password_stdin, interrupted.is_none())? };
    let (config, key) = match &interrupted {
        Some(existing) => {
            let key = unlock_config(&password, existing).map_err(|e| format!("{e}: an interrupted init left \
                .transcrypt/config under another passphrase; rerun with that one, or start over: {START_OVER}"))?;
            (transcrypt_rs::config_array(existing)?.to_owned(), key)
        },
        None => new_config(&password)?,
    };
    let rollback = Rollback {
        root: root.to_owned(),
        config: config.to_vec(),
        attributes_before: worktree_attributes(root)?,
        hook_preexisted: HOOKS.map(|(name, _)| fs::symlink_metadata(hook_path(root, name)).is_ok()),
    };
    let staging = staging_dir(root)?;
    let result = (|| -> Result<(), String> {
        if interrupted.is_none() {
            write_repository_file(root, &staging, Path::new(CONFIG_PATH), &config)?;
        }
        edit_attributes(root, &staging, false, |_| Ok(()))?;
        install(root)?;
        activate(root, &config, &key, options.private, options.timeout)?;
        git(root, &["add", "--", CONFIG_PATH, ".gitattributes"])?;
        Ok(())
    })();
    drop(staging);
    if let Err(e) = result {
        // A resumed initialization keeps the state it resumed from, so that
        // it can be rerun again.
        if interrupted.is_some() {
            return Err(format!("{e}; rerun to complete the initialization"));
        }
        rollback.run();
        return Err(format!("{e}; initialization rolled back"));
    }
    eprintln!("Initialized v3 and unlocked this checkout{}.", if options.private { " (private mode)" } else { "" });
    Ok(rollback)
}

/// `unlock`: authenticate the passphrase against the committed config
/// before changing anything, install the filters and hooks, keep the key
/// (stored, or in the private agent) and decrypt the worktree.
pub(crate) fn unlock(root: &Path, options: &Options) -> Result<(), String> {
    let config = load_config(root)?;
    check_hook_available(root)?;
    let current = credential::state_to_unlock(root, &config)?;
    if current.key().is_some_and(|key| key.private() == options.private) {
        install(root)?;
        let n = if options.hydrate { hydrate(root)? } else { 0 };
        eprintln!("Already unlocked; decrypted {n} file(s).");
        return Ok(());
    }
    let password = passphrase(options.password_stdin, false)?;
    let key = unlock_config(&password, &config)?; // Authenticate BEFORE any persistent writes.
    install(root)?;
    activate(root, &config, &key, options.private, options.timeout)?;
    let mode = if options.private { "private mode: key in memory until lock or logout" }
        else { "key stored in .git/transcrypt-v3/key until lock" };
    if !options.hydrate {
        eprintln!("Unlocked ({mode}). Run `transcrypt-rs hydrate` to decrypt the worktree.");
        return Ok(());
    }
    // Unlocking is complete; hydration is a separate, all-or-nothing step
    // whose refusal must not hide that the checkout is now unlocked.
    match hydrate(root) {
        Ok(n) => eprintln!("Unlocked ({mode}); decrypted {n} file(s)."),
        Err(e) => eprintln!("Unlocked ({mode}), but decryption changed nothing: {e}\n\
            Inspect with `transcrypt-rs status`, then run `transcrypt-rs hydrate`."),
    }
    Ok(())
}

/// Remove v3 from this checkout. The worktree must be (or is first made, by
/// `lock`) ciphertext only, since without the filter Git would store any
/// plaintext as is. Then the filter configuration, the hooks v3 installed
/// (only if unchanged) and the credential directory are removed. The
/// committed `.transcrypt/config` and `.gitattributes` stay: removing them
/// from the repository is a commit, and the history stays encrypted.
pub(crate) fn uninstall(root: &Path) -> Result<(), String> {
    // On a branch without a v3 config (made before `init`) there is nothing
    // to lock here; other worktrees must still hold no plaintext.
    if let Ok(config) = load_config(root) {
        if Key::load(root, &config)?.is_some() {
            lock(root)?;
        }
        worktree_encrypted(root, &config)
            .map_err(|e| format!("{e}; unlock, commit or discard it, and lock before uninstalling"))?;
    }
    others_encrypted(root)?;
    credential::forget(root)?;
    remove_filters(root);
    remove_hooks(root)?;
    let attributes = common_dir(root).join("info/attributes");
    if let Ok(text) = fs::read_to_string(&attributes) {
        if text.lines().any(|l| l == LEGACY_MERGE_ATTRIBUTE) {
            let kept: Vec<&str> = text.lines().filter(|l| *l != LEGACY_MERGE_ATTRIBUTE).collect();
            let mut rewritten = kept.join("\n");
            if !rewritten.is_empty() { rewritten.push('\n'); }
            let _ = fs::write(&attributes, rewritten);
        }
    }
    let _ = fs::remove_dir(common_dir(root).join("transcrypt-v3"));
    for dir in ["transcrypt-v3-staging", "transcrypt-v3-scratch"] {
        let _ = fs::remove_dir(git_dir(root).join(dir));
    }
    eprintln!("Removed transcrypt-rs from this checkout; protected files stay encrypted.\n\
        WARNING: without the filter, a protected file you add now is committed as plaintext. To stop \
        using v3, commit the removal of the `transcrypt` lines and .transcrypt/ (history stays encrypted).");
    Ok(())
}

/// Read-only summary for users. Never writes to the worktree, index or
/// credential directory.
pub(crate) fn status(root: &Path) -> Result<(), String> {
    let config = match load_config(root) {
        Ok(config) => config,
        Err(e) => {
            println!("repository: not initialized for v3 ({e})");
            return Ok(());
        }
    };
    let id = transcrypt_rs::config_id(&config);
    println!("repository: v3 config {}", short_id(&id));
    let unlock = credential::lookup(root, &config)?;
    println!("key:        {}", match &unlock {
        Unlock::Unlocked(key) if !key.private() => "unlocked (stored in .git/transcrypt-v3/key)",
        Unlock::Unlocked(_) => "unlocked (private: held in memory by an agent)",
        Unlock::Locked => "locked",
        Unlock::Stale => "locked: the stored key does not match .transcrypt/config (rekeyed?); run unlock",
    });
    let key = unlock.key();
    let mut counts = [0usize; BUCKETS];
    let mut count = |state: FileState, name: &str| {
        counts[state.bucket() as usize] += 1;
        println!("  {:<LABEL_WIDTH$} {name}", state.label());
    };
    let index = index_with_conflicts(root)?;
    for path in protected_paths(root, &index.conflicted)? {
        count(FileState::Conflicted, &String::from_utf8_lossy(&path));
    }
    for staged in protected_entries(root, index.merged, Attributes::Staged)? {
        count(file_state(root, &id, key, &staged).unwrap_or(FileState::Error), &staged.name());
    }
    let [ciphertext, plaintext, modified, other] = counts;
    println!("protected:  {ciphertext} ciphertext, {plaintext} plaintext, {modified} modified, {other} other");
    if other > 0 && key.is_some() {
        println!("note:       the pre-commit hook encrypts files you staged unencrypted and re-encrypts files you \
            renamed; files encrypted under an earlier config (cherry-picked or rebased across a rekey) need \
            `transcrypt-rs reencrypt`");
    }
    let untracked = git(root, &["ls-files", "--others", "--exclude-standard", "-z"])?;
    let untracked: Vec<&[u8]> = records(&untracked).collect();
    let loose = protected_flags(root, &untracked, Attributes::Worktree)?.into_iter().filter(|p| *p).count();
    if loose > 0 {
        println!("note:       {loose} untracked protected file(s); `git add` encrypts them");
    }
    if key.is_some() && ciphertext > 0 {
        println!("hint:       run `transcrypt-rs hydrate` to decrypt ciphertext in the worktree");
    }
    if hooks_bypassed(root) {
        println!("warning:    {HOOKS_BYPASSED}");
    }
    Ok(())
}

/// What `status` says of one protected file.
#[derive(Clone, Copy)]
enum FileState {
    Conflicted,
    Unsupported,
    OtherConfig,
    Unencrypted,
    Deleted,
    Ciphertext,
    ModifiedOrPlaintext,
    Plaintext,
    Modified,
    RenamedOrInvalid,
    Error,
}

/// The categories `status` counts, in the order it prints them.
#[derive(Clone, Copy)]
enum Bucket { Ciphertext, Plaintext, Modified, Other }
/// The number of `Bucket`s (`Other` is the last).
const BUCKETS: usize = Bucket::Other as usize + 1;
/// The column width of a `FileState` label in `status`.
const LABEL_WIDTH: usize = 22;

impl FileState {
    fn label(self) -> &'static str {
        match self {
            FileState::Conflicted => "conflicted",
            FileState::Unsupported => "unsupported mode",
            FileState::OtherConfig => "other config (reencrypt)",
            FileState::Unencrypted => "staged unencrypted",
            FileState::Deleted => "deleted",
            FileState::Ciphertext => "ciphertext",
            FileState::ModifiedOrPlaintext => "modified or plaintext",
            FileState::Plaintext => "plaintext",
            FileState::Modified => "modified",
            FileState::RenamedOrInvalid => "renamed or invalid",
            FileState::Error => "error",
        }
    }

    fn bucket(self) -> Bucket {
        match self {
            FileState::Ciphertext => Bucket::Ciphertext,
            FileState::Plaintext => Bucket::Plaintext,
            FileState::Conflicted | FileState::Modified | FileState::ModifiedOrPlaintext | FileState::Deleted =>
                Bucket::Modified,
            FileState::Unsupported | FileState::OtherConfig | FileState::Unencrypted | FileState::RenamedOrInvalid
                | FileState::Error => Bucket::Other,
        }
    }
}

/// What `status` says of one staged protected file.
fn file_state(root: &Path, id: &[u8; transcrypt_v3_core::ID_LEN], key: Option<&Key>, staged: &Staged)
    -> Result<FileState, String>
{
    if !staged.regular { return Ok(FileState::Unsupported); }
    let object = git_blob(root, &staged.oid)?;
    if !record_envelope_ok(&object, id) {
        return Ok(if parse_file_header(&object).is_ok() { FileState::OtherConfig } else { FileState::Unencrypted });
    }
    let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? else { return Ok(FileState::Deleted) };
    let (worktree, _) = target.read()?;
    if *worktree == object { return Ok(FileState::Ciphertext); }
    let Some(key) = key else { return Ok(FileState::ModifiedOrPlaintext) };
    Ok(match key.open(&staged.path, &object) {
        Ok(plaintext) if *worktree == *plaintext => FileState::Plaintext,
        Ok(_) => FileState::Modified,
        Err(_) => FileState::RenamedOrInvalid,
    })
}

/// Check that every local protection is actually in place, and say what
/// cannot be checked from here. Exits non-zero if a protection is missing.
pub(crate) fn doctor(root: &Path) -> Result<(), String> {
    let mut failures = 0;
    let mut report = |ok: bool, what: &str| {
        if !ok { failures += 1; }
        println!("{} {what}", if ok { "ok  " } else { "FAIL" });
    };
    let config = load_config(root);
    report(config.is_ok(), "committed .transcrypt/config is a valid v3 config");
    let unlock = match &config {
        Ok(config) => Some(credential::lookup(root, config)?),
        Err(_) => None,
    };
    let key = unlock.as_ref().and_then(Unlock::key);
    // Filters and drivers, as Git will resolve them (any config scope).
    let effective = |key: &str| git(root, &["config", "--get", key]).ok()
        .map(|v| String::from_utf8_lossy(&v).trim_end().to_owned());
    match expected_config() {
        Ok(settings) => for (name, value) in settings {
            let what = if value == "true" { format!("{name} is true") }
                else if name.ends_with(".name") { format!("{name} is set") }
                else { format!("{name} runs this transcrypt-rs") };
            report(effective(name).as_deref() == Some(value.as_str()), &what);
        },
        Err(e) => report(false, &e),
    }
    let entries = indexed_files(root);
    let top = entries.as_ref().ok().and_then(|e| e.iter().find(|e| e.path == ATTRIBUTES_NAME)).map(|e| e.oid.clone());
    if config.is_ok() {
        match entries.and_then(|entries| staged_protected(root, entries)) {
            Ok(protected) if protected.is_empty() => println!("note no tracked file is protected yet: \
                `transcrypt-rs protect PATTERN` (for example .env)"),
            Ok(protected) => println!("note {} tracked file(s) protected by .gitattributes", protected.len()),
            Err(e) => report(false, &format!("protected-file selection: {e}")),
        }
        let checked = check_index(root, key);
        report(checked.is_ok(), &match checked {
            Ok(_) if key.is_some() => "every staged protected file authenticates at its path".to_owned(),
            Ok(_) => "every staged protected file has the v3 envelope (unlock to authenticate)".to_owned(),
            Err(e) => format!("staged index: {e}"),
        });
    }
    for (name, command) in HOOKS.into_iter().filter(|(name, _)| hook_required(name)) {
        let path = hook_path(root, name);
        let installed = fs::read_to_string(&path).ok() == hook_script(command).ok()
            && os::runnable(&path);
        report(installed, &format!("{name} hook installed"));
    }
    report(!hooks_bypassed(root), "Git runs the hooks in .git/hooks (core.hooksPath unset)");
    report(macro_resolves(root, &git_dir(root), top.as_deref()).unwrap_or(false),
        "the `transcrypt` macro sets filter=transcrypt-v3 for the next commit");
    // Attribute files outside the repository apply only here, and could
    // silently unprotect files that the committed .gitattributes protect.
    let overrides = filter_overrides(root);
    report(overrides.is_empty(), &if overrides.is_empty() {
        "no local attribute file overrides `filter`".to_owned()
    } else {
        format!("no local attribute file overrides `filter` (check {})", overrides.join(", "))
    });
    println!("note key {}", match &unlock {
        Some(Unlock::Unlocked(key)) if !key.private() => "stored in .git/transcrypt-v3/key (unlocked)",
        Some(Unlock::Unlocked(_)) => "held in memory by the private agent (unlocked)",
        Some(Unlock::Stale) => "stored, but for another config (rekeyed?): run unlock",
        _ => "none (locked)",
    });
    if key.is_some_and(Key::private) {
        println!("note {}", os::CHECKOUTS_PRIVATE[os::checkouts_private() as usize]);
    }
    println!("note remote enforcement cannot be checked from here: deploy contrib/v3/pre-receive or \
        `transcrypt-rs audit` in CI on every shared remote");
    if failures > 0 {
        return Err(format!("{failures} protection(s) missing; run `transcrypt-rs unlock` to reinstall filters and hooks"));
    }
    Ok(())
}
