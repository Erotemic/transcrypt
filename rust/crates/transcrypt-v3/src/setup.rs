//! Repository setup: init, unlock, protect and unprotect, rekey, uninstall,
//! the Git filters, drivers and hooks, and `doctor`, which checks that all of
//! them are in place.

use std::{
    env,
    ffi::OsString,
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
};
use std::os::unix::{ffi::OsStrExt, fs::OpenOptionsExt};
use transcrypt_v3::{initialize_config, unlock_config, SecretKey};
use transcrypt_v3_core::{parse_file_header, SALT_LEN};
use crate::{
    credential::{self, Key, State},
    git::*,
    lifecycle::*,
    load_config, passphrase, session, umask_is_private,
    worktree::{find_protected, indexed_path, staging_dir, write_repository_file, Staging},
    Options,
};

pub(crate) const HOOKS_BYPASSED: &str = "core.hooksPath is set, so Git does not run the v3 pre-commit and \
    pre-push checks installed in .git/hooks";

/// Whether Git is configured to run hooks from somewhere other than
/// `.git/hooks`, where v3 installs its checks.
pub(crate) fn hooks_bypassed(root: &Path) -> bool {
    git(root, &["config", "core.hooksPath"]).map(|v| !v.trim_ascii().is_empty()).unwrap_or(false)
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
        ("filter.transcrypt-v3.clean", format!("{program} clean %f")),
        ("filter.transcrypt-v3.smudge", format!("{program} smudge %f")),
        ("filter.transcrypt-v3.required", "true".into()),
        // Preferred by Git when present: one process per Git command.
        ("filter.transcrypt-v3.process", format!("{program} filter-process")),
        ("merge.transcrypt-v3.name", "transcrypt-v3: merge decrypted protected files".into()),
        ("merge.transcrypt-v3.driver", format!("{program} merge %O %A %B %P")),
        ("diff.transcrypt-v3.command", format!("{program} diff")),
    ])
}

/// The committed attribute macro: a pattern followed by `transcrypt` is
/// encrypted (`filter`), diffed and merged decrypted (`diff`, `merge`, local
/// drivers; a checkout without them sees binary files), and never
/// line-ending converted (`-text`: Git would convert the ciphertext).
const MACRO: &[u8] = b"[attr]transcrypt filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text";
const MACRO_COMMENT: &[u8] = b"# transcrypt-v3: files matching a pattern marked `transcrypt` are encrypted in Git";
/// The local attribute line that older versions wrote to
/// `.git/info/attributes`; the macro replaces it.
const LEGACY_MERGE_ATTRIBUTE: &str = "*.secret diff=transcrypt-v3 merge=transcrypt-v3";

fn install_filters(root: &Path) -> Result<(), String> {
    for (k, value) in expected_config()? {
        git(root, &["config", "--local", k, &value])?;
    }
    Ok(())
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

/// Whether `text` is a hook this or an earlier v3 version installed.
fn ours(name: &str, command: &str, text: &str) -> bool {
    let Ok(program) = program() else { return false };
    let legacy = if name == "pre-commit" { Some("verify-index") } else { None };
    [Some(command), legacy].into_iter().flatten().any(|c| text == format!("#!/bin/sh\nexec {program} {c}\n"))
}

fn hook_path(root: &Path, name: &str) -> PathBuf {
    common_dir(root).join("hooks").join(name)
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
    fs::create_dir_all(common_dir(root).join("hooks")).map_err(|e| format!("cannot create .git/hooks: {e}"))?;
    for (name, command) in HOOKS {
        let path = hook_path(root, name);
        let script = hook_script(command)?;
        if let Ok(text) = fs::read_to_string(&path) {
            if text == script { continue; }
            if !ours(name, command, &text) { continue; }
            fs::remove_file(&path).map_err(|e| format!("cannot replace the {name} hook: {e}"))?;
        } else if fs::symlink_metadata(&path).is_ok() {
            continue;
        }
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true).mode(0o700);
        options.open(path).map_err(|e| format!("cannot install {name} hook: {e}"))?
            .write_all(script.as_bytes()).map_err(|e| format!("cannot write {name} hook: {e}"))?;
    }
    if hooks_bypassed(root) {
        eprintln!("warning: {HOOKS_BYPASSED}");
    }
    Ok(())
}

fn remove_hooks(root: &Path) -> Result<(), String> {
    for (name, command) in HOOKS {
        let path = hook_path(root, name);
        if fs::read_to_string(&path).is_ok_and(|text| ours(name, command, &text)) {
            fs::remove_file(&path).map_err(|e| format!("cannot remove {name} hook: {e}"))?;
        }
    }
    Ok(())
}

/// Make `key` the credential of this checkout, in the requested mode, and
/// remove the other mode's.
fn activate(root: &Path, config: &[u8], key: &SecretKey, private: bool, idle: Option<std::time::Duration>)
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
    let rollback = init_with_rollback(root, options)?;
    if !options.patterns.is_empty() {
        if let Err(e) = protect(root, &options.patterns) {
            rollback.run();
            return Err(format!("{e}; initialization rolled back"));
        }
    } else {
        eprintln!("Choose what to encrypt, for example:\n  transcrypt-v3 protect .env 'secrets/**'");
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
        let _ = git(root, &["reset", "-q", "--", ".transcrypt/config", ".gitattributes"]);
        if fs::read(root.join(".transcrypt/config")).ok().as_deref() == Some(&self.config[..]) {
            let _ = fs::remove_file(root.join(".transcrypt/config"));
            let _ = fs::remove_dir(root.join(".transcrypt"));
        }
        match (&self.attributes_before, staging_dir(root)) {
            (Some(before), Ok(staging)) => {
                let _ = write_repository_file(root, &staging, Path::new(".gitattributes"), before);
            },
            (None, _) => { let _ = fs::remove_file(root.join(".gitattributes")); },
            _ => {},
        }
        for ((name, command), preexisted) in HOOKS.into_iter().zip(self.hook_preexisted) {
            let hook = hook_path(root, name);
            if !preexisted && fs::read_to_string(&hook).is_ok_and(|t| ours(name, command, &t)) {
                let _ = fs::remove_file(&hook);
            }
        }
        remove_filters(root);
        let _ = credential::forget(root);
        let _ = session::stop(root, &self.config);
    }
}

/// Initialize (without protecting anything yet); on failure everything is
/// rolled back, on success the caller gets the rollback for later steps.
pub(crate) fn init_with_rollback(root: &Path, options: &Options) -> Result<Rollback, String> {
    if fs::symlink_metadata(root.join(".transcrypt")).is_ok() {
        return Err(".transcrypt already exists: this repository is set up; run `transcrypt-v3 unlock`".into());
    }
    check_hook_available(root)?;
    let password = passphrase(options.password_stdin, true)?;
    let mut salt = [0u8; SALT_LEN];
    getrandom::fill(&mut salt).map_err(|_| "OS randomness unavailable")?;
    let (config, key) = initialize_config(&password, &salt)?;
    let rollback = Rollback {
        root: root.to_owned(),
        config: config.to_vec(),
        attributes_before: find_protected(root, Path::new(".gitattributes"))?
            .map(|f| f.read().map(|(bytes, _)| bytes.to_vec())).transpose()?,
        hook_preexisted: HOOKS.map(|(name, _)| fs::symlink_metadata(hook_path(root, name)).is_ok()),
    };
    let staging = staging_dir(root)?;
    let result = (|| -> Result<(), String> {
        write_repository_file(root, &staging, Path::new(".transcrypt/config"), &config)?;
        edit_attributes(root, &staging, |_| Ok(()))?;
        install_filters(root)?;
        install_hooks(root)?;
        activate(root, &config, &key, options.private, options.timeout)?;
        git(root, &["add", "--", ".transcrypt/config", ".gitattributes"])?;
        Ok(())
    })();
    drop(staging);
    if let Err(e) = result {
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
    let current = credential::state(root, &config)?;
    if matches!(current, State::Unlocked { private } if private == options.private) {
        install_filters(root)?;
        install_hooks(root)?;
        let n = if options.hydrate { hydrate(root)? } else { 0 };
        eprintln!("Already unlocked; decrypted {n} file(s).");
        return Ok(());
    }
    let password = passphrase(options.password_stdin, false)?;
    let key = unlock_config(&password, &config)?; // Authenticate BEFORE any persistent writes.
    install_filters(root)?;
    install_hooks(root)?;
    activate(root, &config, &key, options.private, options.timeout)?;
    let mode = if options.private { "private mode: key in memory until lock or logout" }
        else { "key stored in .git/transcrypt-v3/key until lock" };
    if !options.hydrate {
        eprintln!("Unlocked ({mode}). Run `transcrypt-v3 hydrate` to decrypt the worktree.");
        return Ok(());
    }
    // Unlocking is complete; hydration is a separate, all-or-nothing step
    // whose refusal must not hide that the checkout is now unlocked.
    match hydrate(root) {
        Ok(n) => eprintln!("Unlocked ({mode}); decrypted {n} file(s)."),
        Err(e) => eprintln!("Unlocked ({mode}), but decryption changed nothing: {e}\n\
            Inspect with `transcrypt-v3 status`, then run `transcrypt-v3 hydrate`."),
    }
    Ok(())
}

/// The top-level `.gitattributes` as it was, in the worktree and the index,
/// so that a command that fails after editing it can put both back.
struct AttributesUndo {
    worktree: Option<Vec<u8>>,
    staged: Option<(String, String)>,
}

impl AttributesUndo {
    fn capture(root: &Path) -> Result<AttributesUndo, String> {
        Ok(AttributesUndo {
            worktree: find_protected(root, Path::new(".gitattributes"))?
                .map(|f| f.read().map(|(bytes, _)| bytes.to_vec())).transpose()?,
            staged: indexed_files(root)?.into_iter().find(|e| e.path == b".gitattributes").map(|e| (e.mode, e.oid)),
        })
    }

    fn restore(&self, root: &Path) {
        match (&self.worktree, staging_dir(root)) {
            (Some(bytes), Ok(staging)) => { let _ = write_repository_file(root, &staging, Path::new(".gitattributes"), bytes); },
            (None, _) => { let _ = fs::remove_file(root.join(".gitattributes")); },
            _ => {},
        }
        let _ = match &self.staged {
            Some((mode, oid)) => git_with_input(root, &["update-index", "-z", "--index-info"],
                format!("{mode} {oid}\t.gitattributes\0").as_bytes()),
            None => git(root, &["update-index", "--force-remove", "--", ".gitattributes"]),
        };
    }
}

/// Patterns as the user wrote them must select what they name. Git applies
/// `.gitattributes` patterns to files only, relative to the top-level
/// directory, without `./`, and has no negation: refuse what would silently
/// select nothing.
fn check_pattern(root: &Path, pattern: &[u8]) -> Result<Vec<u8>, String> {
    let shown = String::from_utf8_lossy(pattern).into_owned();
    let mut pattern = pattern;
    while let Some(rest) = pattern.strip_prefix(b"./") { pattern = rest; }
    if pattern.starts_with(b"!") {
        return Err(format!("{shown}: .gitattributes has no negative patterns; to exclude a file from a \
            protected pattern, add `PATH -filter -diff -merge` to .gitattributes"));
    }
    if pattern.ends_with(b"/") || root.join(std::ffi::OsStr::from_bytes(pattern)).is_dir() {
        let dir = String::from_utf8_lossy(pattern.strip_suffix(b"/").unwrap_or(pattern)).into_owned();
        return Err(format!("{shown}: attribute patterns select files, not directories; use '{dir}/**' \
            for everything below it"));
    }
    Ok(pattern.to_vec())
}

/// After `.gitattributes` was edited: a pattern that names an existing file
/// must select it (a backslash or bracket in a name is a glob character).
fn check_selects(root: &Path, patterns: &[Vec<u8>]) -> Result<(), String> {
    let files: Vec<&[u8]> = patterns.iter().map(Vec::as_slice)
        .filter(|p| root.join(std::ffi::OsStr::from_bytes(p)).is_file()).collect();
    for (path, protected) in files.iter().zip(protected_flags(root, &files, Attributes::Worktree)?) {
        if !protected {
            return Err(format!("the pattern {} does not select the file of that name (Git reads `\\`, `*`, \
                `?` and `[` in patterns as glob characters); escape them, e.g. `[[]` for `[`",
                String::from_utf8_lossy(path)));
        }
    }
    Ok(())
}

/// Whether an attribute line defines the `transcrypt` macro.
fn defines_macro(line: &[u8]) -> bool {
    line.trim_ascii().strip_prefix(b"[attr]transcrypt")
        .is_some_and(|rest| rest.is_empty() || rest[0].is_ascii_whitespace())
}

/// One `.gitattributes` line, as bytes, without its newline.
type Line = Vec<u8>;

/// Rewrite the top-level `.gitattributes` through `edit` (after making
/// sure it defines the `transcrypt` macro), write it safely and stage it.
fn edit_attributes(root: &Path, staging: &Staging, edit: impl FnOnce(&mut Vec<Line>) -> Result<(), String>)
    -> Result<(), String>
{
    let existing = find_protected(root, Path::new(".gitattributes"))?
        .map(|f| f.read().map(|(bytes, _)| bytes.to_vec())).transpose()?.unwrap_or_default();
    let mut lines: Vec<Line> = existing.split(|b| *b == b'\n').map(<[u8]>::to_vec).collect();
    if lines.last().is_some_and(Vec::is_empty) { lines.pop(); }
    // Another definition of the macro would silently replace ours (Git uses
    // the last one), and `PATTERN transcrypt` would select nothing.
    if let Some(other) = lines.iter().find(|l| defines_macro(l) && *l != MACRO) {
        return Err(format!(".gitattributes already defines the `transcrypt` macro differently (`{}`); \
            remove or rename that definition first", String::from_utf8_lossy(other)));
    }
    if !lines.iter().any(|l| l == MACRO) {
        // Macros may only be defined in the top-level file; put it first.
        lines.splice(0..0, [MACRO_COMMENT.to_vec(), MACRO.to_vec()]);
    }
    edit(&mut lines)?;
    let mut text = lines.join(&b'\n');
    text.push(b'\n');
    if text != existing {
        write_repository_file(root, staging, Path::new(".gitattributes"), &text)?;
        // Repository metadata must stay readable: refuse a pattern that
        // selects it (Git would then fail to stage .gitattributes itself).
        let reserved: [&[u8]; 3] = [b".gitattributes", b".transcrypt/config", b".gitmodules"];
        let selected = protected_flags(root, &reserved, Attributes::Worktree)?;
        if let Some((path, _)) = reserved.iter().zip(selected).find(|(_, p)| *p) {
            if existing.is_empty() {
                let _ = fs::remove_file(root.join(".gitattributes"));
            } else {
                write_repository_file(root, staging, Path::new(".gitattributes"), &existing)?;
            }
            return Err(format!("that pattern would encrypt {}, which Git and v3 must read unencrypted; \
                use a narrower pattern", String::from_utf8_lossy(path)));
        }
    }
    git(root, &["add", "--", ".gitattributes"]).map(|_| ())
}

/// A `.gitattributes` line protecting `pattern`. Git reads a pattern that
/// starts with `"` as a C-style quoted string, so names with spaces, quotes,
/// backslashes or control characters are quoted.
fn protect_line(pattern: &[u8]) -> Result<Line, String> {
    if pattern.is_empty() || pattern.contains(&0) || pattern.starts_with(b"[attr]") || pattern.starts_with(b"#") {
        return Err(format!("invalid pattern {:?}", String::from_utf8_lossy(pattern)));
    }
    // Git ends an unquoted pattern at the first blank.
    let plain = !pattern.starts_with(b"\"") && pattern.iter().all(|b| *b > b' ' && *b != 0x7f);
    let mut line = Vec::new();
    if plain {
        line.extend_from_slice(pattern);
    } else {
        line.push(b'"');
        for &b in pattern {
            match b {
                b'"' => line.extend_from_slice(b"\\\""),
                b'\\' => line.extend_from_slice(b"\\\\"),
                b'\n' => line.extend_from_slice(b"\\n"),
                b'\t' => line.extend_from_slice(b"\\t"),
                b if b < b' ' || b == 0x7f => line.extend_from_slice(format!("\\{b:03o}").as_bytes()),
                b => line.push(b),
            }
        }
        line.push(b'"');
    }
    line.extend_from_slice(b" transcrypt");
    Ok(line)
}

/// `protect PATTERN...`: add a `PATTERN transcrypt` line for each, stage
/// `.gitattributes`, and encrypt in the index every tracked file the
/// patterns now select (the pre-commit hook would do it at the next commit
/// anyway; doing it now makes `git status` and `git diff --cached` honest).
pub(crate) fn protect(root: &Path, patterns: &[OsString]) -> Result<(), String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let patterns = patterns.iter().map(|p| check_pattern(root, p.as_bytes())).collect::<Result<Vec<_>, _>>()?;
    let lines = patterns.iter().map(|p| protect_line(p)).collect::<Result<Vec<_>, _>>()?;
    let undo = AttributesUndo::capture(root)?;
    let result = (|| -> Result<(), String> {
        let staging = staging_dir(root)?;
        edit_attributes(root, &staging, |existing| {
            for line in lines {
                if !existing.contains(&line) { existing.push(line); }
            }
            Ok(())
        })?;
        drop(staging);
        check_selects(root, &patterns)?;
        // Seal every selected file still staged in plaintext: newly selected
        // ones, and ones a hand-edited `.gitattributes` selected earlier.
        let protected = staged_protected(root, indexed_files(root)?)?;
        let selected: Vec<Vec<u8>> = protected.iter().map(|e| e.path.clone()).collect();
        let sealed = seal_staged(root, &key, &selected)?;
        match protected.len() {
            0 => eprintln!("Protected patterns added; no tracked file matches yet. `git add` encrypts matching files."),
            n => eprintln!("{n} tracked file(s) protected{}.",
                if sealed > 0 { format!("; {sealed} of them encrypted in the index just now") } else { String::new() }),
        }
        if sealed > 0 && git(root, &["rev-parse", "-q", "--verify", "HEAD^{commit}"]).is_ok() {
            eprintln!("Files that were committed before they were protected stay readable in earlier commits: \
                if the history is public, change those secrets.");
        }
        Ok(())
    })();
    if result.is_err() { undo.restore(root); }
    result
}

/// `unprotect PATTERN...`: remove the `PATTERN transcrypt` lines, and stage
/// the plaintext of each tracked file that is no longer protected (its next
/// commit publishes it unencrypted, which is the point). Every record to be
/// released is decrypted first; on any error `.gitattributes` and the index
/// are restored.
pub(crate) fn unprotect(root: &Path, patterns: &[OsString]) -> Result<(), String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let patterns = patterns.iter().map(|p| check_pattern(root, p.as_bytes())).collect::<Result<Vec<_>, _>>()?;
    let lines = patterns.iter().map(|p| protect_line(p)).collect::<Result<Vec<_>, _>>()?;
    let before = staged_protected(root, indexed_files(root)?)?;
    let undo = AttributesUndo::capture(root)?;
    let result = (|| -> Result<Vec<Vec<u8>>, String> {
        let staging = staging_dir(root)?;
        edit_attributes(root, &staging, |existing| {
            for line in &lines {
                let n = existing.len();
                existing.retain(|l| l != line);
                if existing.len() == n {
                    return Err(format!("no `{}` line in .gitattributes; edit it directly to change other rules",
                        String::from_utf8_lossy(line)));
                }
            }
            Ok(())
        })?;
        let still: Vec<Vec<u8>> = staged_protected(root, indexed_files(root)?)?.into_iter().map(|e| e.path).collect();
        // Decrypt everything before changing any file or index entry.
        let mut released = Vec::new();
        for staged in before.into_iter().filter(|e| !still.contains(&e.path)) {
            let plaintext = open_staged(root, &key, &staged)?;
            released.push((staged, plaintext));
        }
        // A worktree file that still holds the record gets its plaintext
        // (harmless if a later step fails); the index changes last.
        for (staged, plaintext) in &released {
            if let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? {
                let (worktree, stamp) = target.read()?;
                if *worktree == git_blob(root, &staged.oid)? {
                    target.replace(&staging, plaintext, &stamp, key.private())?;
                }
            }
        }
        let mut index_info = Vec::new();
        for (staged, plaintext) in &released {
            index_info.extend_from_slice(format!("{} {}\t", staged.mode, hash_object(root, plaintext)?).as_bytes());
            index_info.extend_from_slice(&staged.path);
            index_info.push(0);
        }
        if !index_info.is_empty() {
            git_with_input(root, &["update-index", "-z", "--index-info"], &index_info)?;
        }
        Ok(released.into_iter().map(|(staged, _)| staged.path).collect())
    })();
    let released = match result {
        Ok(released) => released,
        Err(e) => { undo.restore(root); return Err(e); },
    };
    eprintln!("{} file(s) are no longer protected; their next commit stores them UNENCRYPTED:", released.len());
    for path in &released {
        eprintln!("  {}", String::from_utf8_lossy(path));
    }
    Ok(())
}

/// Change the passphrase. Every protected file must be committed (no edit
/// is mixed into the re-encryption). A fresh salt and key give a new config;
/// every staged record is re-encrypted under it, and all of them plus the
/// config are staged in one index update for the user to commit. Only then
/// does the worktree config, written like a protected file (never through a
/// symlink), and the credential switch to the new key. Commits made before
/// keep their old records, readable with the old passphrase.
pub(crate) fn rekey(root: &Path, options: &Options) -> Result<(), String> {
    let old_config = load_config(root)?;
    let old_key = Key::load(root, &old_config)?.ok_or("unlock with the current passphrase first")?;
    let password = passphrase(options.password_stdin, true)?;
    // No hydrate or lock may run meanwhile.
    let staging = staging_dir(root)?;
    // Decrypt everything first, then require that each file is exactly the
    // plaintext of its staged record.
    hydrate_locked(root, &staging)?;
    let verified = check_index(root, Some(&old_key))?;
    let mut plaintexts = Vec::new();
    for staged in &verified.protected {
        let plaintext = old_key.open(&staged.path, &git_blob(root, &staged.oid)?)?;
        let unchanged = match find_protected(root, &indexed_path(&staged.path)?)? {
            Some(target) => *target.read()?.0 == *plaintext,
            None => false,
        };
        if !unchanged {
            return Err(format!("{} has uncommitted changes (or was deleted); commit or discard them before \
                rekeying", String::from_utf8_lossy(&staged.path)));
        }
        plaintexts.push((staged, plaintext));
    }
    let mut salt = [0u8; SALT_LEN];
    getrandom::fill(&mut salt).map_err(|_| "OS randomness unavailable")?;
    let (config, key) = initialize_config(&password, &salt)?;
    // The new records, written as Git objects, and one index update.
    let mut index_info = Vec::new();
    for (staged, plaintext) in &plaintexts {
        let record = transcrypt_v3::encrypt_file(&config, &key, &staged.path, plaintext)?;
        index_info.extend_from_slice(format!("{} {}\t", staged.mode, hash_object(root, &record)?).as_bytes());
        index_info.extend_from_slice(&staged.path);
        index_info.push(0);
    }
    index_info.extend_from_slice(format!("100644 {}\t.transcrypt/config\0", hash_object(root, &config)?).as_bytes());
    git_with_input(root, &["update-index", "-z", "--index-info"], &index_info)?;
    let undo = "; run `git reset` to undo the staged rekey";
    write_repository_file(root, &staging, Path::new(".transcrypt/config"), &config)
        .map_err(|e| format!("{e}{undo}"))?;
    if old_key.private() {
        session::stop(root, &old_config)?;
    }
    activate(root, &config, &key, old_key.private(), None)
        .map_err(|e| format!("{e}; the rekey is staged: run `transcrypt-v3 unlock` with the NEW passphrase"))?;
    drop(staging);
    // The worktree plaintext now cleans to the new staged records.
    let paths: Vec<Vec<u8>> = verified.protected.iter().map(|e| e.path.clone()).collect();
    let listing = git(root, &["ls-files", "--stage", "-z"])?;
    reindex(root, &listing, &paths)?;
    eprintln!("Rekeyed {} file(s); the new config and records are staged. Commit them now, e.g.\n  \
        git commit -m 'Rekey transcrypt-v3'\n\
        Earlier commits stay readable with the old passphrase: if it was exposed, change the secrets themselves.",
        plaintexts.len());
    Ok(())
}

/// `reencrypt`: staged protected files still encrypted under an earlier
/// config (a commit cherry-picked or rebased across a `rekey` brings its
/// records unchanged) are opened under that config, found in history and
/// authenticated with its passphrase, at their own path, and re-sealed under
/// the current config. Nothing else changes; the result is staged.
pub(crate) fn reencrypt(root: &Path, options: &Options) -> Result<(), String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let id = transcrypt_v3::config_id(&config);
    let mut stale: Vec<(Staged, Vec<u8>, [u8; transcrypt_v3_core::ID_LEN])> = Vec::new();
    for staged in staged_protected(root, indexed_files(root)?)? {
        let record = git_blob(root, &staged.oid)?;
        if let Ok(found) = parse_file_header(&record) {
            if found != id { stale.push((staged, record, found)); }
        }
    }
    if stale.is_empty() {
        eprintln!("Every staged protected file is encrypted under the current config.");
        return Ok(());
    }
    // The earlier configs, from the history of .transcrypt/config.
    let mut configs: Vec<Vec<u8>> = Vec::new();
    let log = git(root, &["log", "--all", "--format=%H", "--", ".transcrypt/config"])?;
    for commit in String::from_utf8_lossy(&log).lines() {
        if stale.iter().all(|(_, _, found)| configs.iter().any(|c| transcrypt_v3::config_id(c) == *found)) { break; }
        if let Some(oid) = config_blob(root, commit)? {
            let bytes = git_blob(root, &oid)?;
            if transcrypt_v3_core::parse_config(&bytes).is_ok() && !configs.contains(&bytes) { configs.push(bytes); }
        }
    }
    if let Some((staged, _, _)) = stale.iter().find(|(_, _, f)| !configs.iter().any(|c| transcrypt_v3::config_id(c) == *f)) {
        return Err(format!("{} is encrypted under a config that is not in this repository's history",
            String::from_utf8_lossy(&staged.path)));
    }
    let mut index_info = Vec::new();
    let staging = staging_dir(root)?;
    for old in configs.iter().filter(|c| stale.iter().any(|(_, _, f)| *f == transcrypt_v3::config_id(c))) {
        let old_id = transcrypt_v3::config_id(old);
        let names: Vec<String> = stale.iter().filter(|(_, _, f)| *f == old_id)
            .map(|(s, _, _)| String::from_utf8_lossy(&s.path).into_owned()).collect();
        eprintln!("{} encrypted under an earlier config: {}", names.len(), names.join(", "));
        let password = passphrase(options.password_stdin, false)?;
        let old_key = unlock_config(&password, old)?;
        for (staged, record, _) in stale.iter().filter(|(_, _, f)| *f == old_id) {
            let plaintext = transcrypt_v3::decrypt_file(old, &old_key, &staged.path, record)
                .map_err(|e| format!("{}: {e}", String::from_utf8_lossy(&staged.path)))?;
            let sealed = key.clean(&staged.path, &plaintext)?;
            index_info.extend_from_slice(format!("{} {}\t", staged.mode, hash_object(root, &sealed)?).as_bytes());
            index_info.extend_from_slice(&staged.path);
            index_info.push(0);
            if let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? {
                let (worktree, stamp) = target.read()?;
                if *worktree == *record {
                    target.replace(&staging, &plaintext, &stamp, key.private())?;
                }
            }
        }
    }
    git_with_input(root, &["update-index", "-z", "--index-info"], &index_info)?;
    eprintln!("Re-encrypted {} file(s) under the current config; they are staged. Commit them.", stale.len());
    Ok(())
}

/// Remove v3 from this checkout. The worktree must be (or is first made, by
/// `lock`) ciphertext only, since without the filter Git would store any
/// plaintext as is. Then the filter configuration, the hooks v3 installed
/// (only if unchanged) and the credential directory are removed. The
/// committed `.transcrypt/config` and `.gitattributes` stay: removing them
/// from the repository is a commit, and the history stays encrypted.
pub(crate) fn uninstall(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    if Key::load(root, &config)?.is_some() {
        lock(root)?;
    }
    worktree_encrypted(root, &config)
        .map_err(|e| format!("{e}; unlock, commit or discard it, and lock before uninstalling"))?;
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
    eprintln!("Removed transcrypt-v3 from this checkout; protected files stay encrypted.\n\
        WARNING: without the filter, a protected file you add now is committed as plaintext. To stop \
        using v3, commit the removal of the `transcrypt` lines and .transcrypt/ (history stays encrypted).");
    Ok(())
}

/// The attribute files Git reads besides the repository's own
/// `.gitattributes`: `info/attributes` and `core.attributesFile` (by default
/// `$XDG_CONFIG_HOME/git/attributes`).
fn local_attribute_files(root: &Path) -> Vec<PathBuf> {
    let mut files = vec![common_dir(root).join("info/attributes")];
    match git(root, &["config", "--path", "core.attributesFile"]) {
        Ok(path) => files.push(PathBuf::from(String::from_utf8_lossy(&path).trim_end())),
        Err(_) => {
            let base = env::var_os("XDG_CONFIG_HOME").map(PathBuf::from)
                .or_else(|| env::var_os("HOME").map(|h| PathBuf::from(h).join(".config")));
            files.extend(base.map(|b| b.join("git/attributes")));
        },
    }
    files
}

/// The local attribute files that mention `filter` or redefine the
/// `transcrypt` macro.
pub(crate) fn filter_overrides(root: &Path) -> Vec<String> {
    local_attribute_files(root).into_iter().filter(|file| fs::read(file)
        .is_ok_and(|text| text.split(|b| *b == b'\n')
            .any(|line| line.windows(6).any(|w| w == b"filter") || defines_macro(line))))
        .map(|file| file.display().to_string()).collect()
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
    let state = config.as_ref().ok().map(|c| credential::state(root, c)).transpose()?;
    let key = config.as_ref().ok().map(|c| Key::load(root, c)).transpose()?.flatten();
    // Filters and drivers, as Git will resolve them (any config scope).
    let effective = |key: &str| git(root, &["config", "--get", key]).ok()
        .map(|v| String::from_utf8_lossy(&v).trim_end().to_owned());
    match expected_config() {
        Ok(settings) => for (name, value) in settings {
            let what = if value == "true" { format!("{name} is true") }
                else if name.ends_with(".name") { format!("{name} is set") }
                else { format!("{name} runs this transcrypt-v3") };
            report(effective(name).as_deref() == Some(value.as_str()), &what);
        },
        Err(e) => report(false, &e),
    }
    if config.is_ok() {
        match indexed_files(root).and_then(|entries| staged_protected(root, entries)) {
            Ok(protected) if protected.is_empty() => println!("note no tracked file is protected yet: \
                `transcrypt-v3 protect PATTERN` (for example .env)"),
            Ok(protected) => println!("note {} tracked file(s) protected by .gitattributes", protected.len()),
            Err(e) => report(false, &format!("protected-file selection: {e}")),
        }
        let checked = check_index(root, key.as_ref());
        report(checked.is_ok(), &match checked {
            Ok(_) if key.is_some() => "every staged protected file authenticates at its path".to_owned(),
            Ok(_) => "every staged protected file has the v3 envelope (unlock to authenticate)".to_owned(),
            Err(e) => format!("staged index: {e}"),
        });
    }
    for (name, command) in HOOKS.into_iter().filter(|(name, _)| hook_required(name)) {
        let installed = fs::read_to_string(hook_path(root, name)).ok() == hook_script(command).ok();
        report(installed, &format!("{name} hook installed"));
    }
    report(!hooks_bypassed(root), "Git runs the hooks in .git/hooks (core.hooksPath unset)");
    let foreign_macro = fs::read(root.join(".gitattributes")).ok().and_then(|text| text.split(|b| *b == b'\n')
        .find(|l| defines_macro(l) && *l != MACRO).map(|l| String::from_utf8_lossy(l).into_owned()));
    report(foreign_macro.is_none(), &match &foreign_macro {
        None => "the `transcrypt` macro is not redefined in .gitattributes".to_owned(),
        Some(line) => format!("the `transcrypt` macro is not redefined in .gitattributes (found `{line}`)"),
    });
    // Attribute files outside the repository apply only here, and could
    // silently unprotect files that the committed .gitattributes protect.
    let overrides = filter_overrides(root);
    report(overrides.is_empty(), &if overrides.is_empty() {
        "no local attribute file overrides `filter`".to_owned()
    } else {
        format!("no local attribute file overrides `filter` (check {})", overrides.join(", "))
    });
    println!("note key {}", match state {
        Some(State::Unlocked { private: false }) => "stored in .git/transcrypt-v3/key (unlocked)",
        Some(State::Unlocked { private: true }) => "held in memory by the private agent (unlocked)",
        Some(State::Stale) => "stored, but for another config (rekeyed?): run unlock",
        _ => "none (locked)",
    });
    if matches!(state, Some(State::Unlocked { private: true })) {
        println!("note {}", if umask_is_private() {
            "umask is private: Git checkouts write plaintext directly (mode 0600)"
        } else {
            "umask is permissive: Git checkouts write ciphertext; hooks or `hydrate` decrypt with mode 0600"
        });
    }
    println!("note remote enforcement cannot be checked from here: deploy contrib/v3/pre-receive or \
        `transcrypt-v3 audit` in CI on every shared remote");
    if failures > 0 {
        return Err(format!("{failures} protection(s) missing; run `transcrypt-v3 unlock` to reinstall filters and hooks"));
    }
    Ok(())
}
