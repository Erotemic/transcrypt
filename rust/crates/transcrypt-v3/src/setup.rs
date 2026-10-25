//! Repository setup: init, unlock, Git filters and hooks, local ignore
//! rules, and `doctor`, which checks that all of them are in place.

use std::{
    env,
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
};
use std::os::unix::fs::OpenOptionsExt;
use zeroize::Zeroizing;
use transcrypt_v3::{initialize_config, unlock_config};
use crate::{
    check_index,
    git::{git, indexed_files, tree_files},
    hydrate, load_config, protected_path,
    session::{self, Operation},
    umask_is_private, ATTRS,
};
use transcrypt_v3_core::SALT_LEN;

pub(crate) const HOOKS_BYPASSED: &str = "core.hooksPath is set, so Git does not run the v3 pre-commit and \
    pre-push checks (or automatic hydration) installed in .git/hooks";

/// Whether Git is configured to run hooks from somewhere other than
/// `.git/hooks`, where v3 installs its checks.
pub(crate) fn hooks_bypassed(root: &Path) -> bool {
    git(root, &["config", "core.hooksPath"]).map(|v| !v.trim_ascii().is_empty()).unwrap_or(false)
}

fn shell_quote(text: &str) -> String {
    format!("'{}'", text.replace('\'', "'\\''"))
}

/// The Git filter configuration this binary installs.
fn expected_filters() -> Result<[(&'static str, String); 3], String> {
    let bin = env::current_exe().map_err(|_| "cannot resolve current executable")?;
    let path = bin.to_str().ok_or("executable path must be UTF-8")?;
    let program = shell_quote(path);
    Ok([
        ("filter.transcrypt-v3.clean", format!("{program} clean %f")),
        ("filter.transcrypt-v3.smudge", format!("{program} smudge %f")),
        ("filter.transcrypt-v3.required", "true".into()),
    ])
}

fn install_filters(root: &Path) -> Result<(), String> {
    for (k, value) in expected_filters()? {
        git(root, &["config", "--local", k, &value])?;
    }
    Ok(())
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
    let unlocked = config.as_ref().is_ok_and(|c| session::request(root, c, Operation::Ping, &[], &[]).is_ok());
    // Filters, as Git will resolve them (any config scope).
    let effective = |key: &str| git(root, &["config", "--get", key]).ok()
        .map(|v| String::from_utf8_lossy(&v).trim_end().to_owned());
    match expected_filters() {
        Ok(filters) => for (key, value) in filters {
            report(effective(key).as_deref() == Some(value.as_str()), &format!("{key} runs this transcrypt-v3"));
        },
        Err(e) => report(false, &e),
    }
    report(effective("filter.transcrypt-v3.process").is_none(),
        "no filter.transcrypt-v3.process overrides the clean/smudge filters");
    // Attributes a *new* file would get (the worktree .gitattributes).
    for probe in ["transcrypt-v3-probe.secret", "a/b/transcrypt-v3-probe.secret"] {
        let attr = git(root, &["check-attr", "filter", "--", probe]).unwrap_or_default();
        report(attr.ends_with(b": filter: transcrypt-v3\n"), &format!("a new {probe} would be encrypted"));
    }
    if config.is_ok() {
        let checked = check_index(root, unlocked);
        report(checked.is_ok(), &match checked {
            Ok(_) if unlocked => "every staged *.secret authenticates at its path".to_owned(),
            Ok(_) => "every staged *.secret has the v3 envelope (unlock to authenticate)".to_owned(),
            Err(e) => format!("staged index: {e}"),
        });
    }
    for (name, command) in HOOKS {
        let installed = fs::read_to_string(hook_path(root, name)).ok() == expected_hook(command).ok();
        if hook_required(name) {
            report(installed, &format!("{name} hook installed"));
        } else if !installed {
            println!("note {name} hook not installed: run `transcrypt-v3 hydrate` after Git rewrites *.secret files");
        }
    }
    report(!hooks_bypassed(root), "Git runs the hooks in .git/hooks (core.hooksPath unset)");
    println!("note session {}", if unlocked { "unlocked" } else { "locked" });
    println!("note {}", if umask_is_private() {
        "umask is private: Git checkouts write plaintext directly (mode 0600)"
    } else {
        "umask is permissive: Git checkouts write ciphertext; hooks or `hydrate` decrypt with mode 0600"
    });
    println!("note remote enforcement cannot be checked from here: deploy contrib/v3/pre-receive or \
        `transcrypt-v3 audit` in CI on every shared remote");
    if failures > 0 {
        return Err(format!("{failures} protection(s) missing; run `transcrypt-v3 unlock` to reinstall filters and hooks"));
    }
    Ok(())
}

/// Hooks installed by init and unlock, with the v3 command each runs:
/// verify the staged index before every commit, and audit the commits being
/// pushed (which also covers merges, rebases, cherry-picks and
/// `--no-verify` commits that never ran the pre-commit hook).
const HOOKS: [(&str, &str); 5] = [
    ("pre-commit", "verify-index"),
    ("pre-push", "pre-push \"$@\""),
    // After Git writes worktree files (which smudge leaves as ciphertext
    // unless Git's umask makes them private), decrypt them with mode 0600.
    ("post-checkout", "hydrate --auto"),
    ("post-merge", "hydrate --auto"),
    ("post-rewrite", "hydrate --auto"),
];

/// The checks whose absence would let plaintext through. The others only
/// automate hydration: a foreign hook of that name is left alone.
fn hook_required(name: &str) -> bool {
    matches!(name, "pre-commit" | "pre-push")
}

fn expected_hook(command: &str) -> Result<String, String> {
    let bin = env::current_exe().map_err(|_| "cannot locate executable")?;
    let b = bin.to_str().ok_or("executable path must be UTF-8")?;
    Ok(format!("#!/bin/sh\nexec {} {command}\n", shell_quote(b)))
}

fn hook_path(root: &Path, name: &str) -> PathBuf {
    root.join(".git/hooks").join(name)
}

fn check_hook_available(root: &Path) -> Result<(), String> {
    for (name, command) in HOOKS.into_iter().filter(|(name, _)| hook_required(name)) {
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
        if fs::symlink_metadata(&path).is_ok() {
            if !hook_required(name) && fs::read_to_string(&path).ok() != expected_hook(command).ok() {
                eprintln!("note: existing {name} hook left in place; run `transcrypt-v3 hydrate` \
                    after Git commands that rewrite *.secret files");
            }
            continue;
        }
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

pub(crate) fn init(root: &Path, password: Zeroizing<Vec<u8>>) -> Result<(), String> {
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

pub(crate) fn unlock(root: &Path, password: Zeroizing<Vec<u8>>, auto_hydrate: bool) -> Result<(), String> {
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

/// Names that editors and merge tools give to copies of a `*.secret` file.
/// Such copies hold plaintext but are not protected, so `git add -A` would
/// commit them unencrypted. A heuristic backstop, not a guarantee.
const COPY_SUFFIXES: [&[u8]; 10] = [
    b".secret~", b".secret.swp", b".secret.swo", b".secret.swx", b".secret.orig",
    b".secret.bak", b".secret.tmp", b".secret.rej", b".secret.save", b".secret#",
];

pub(crate) fn plaintext_copy_name(path: &[u8]) -> bool {
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
