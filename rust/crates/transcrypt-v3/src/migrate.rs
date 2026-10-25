//! One-time, explicit conversion of a repository protected by Bash
//! transcrypt (the v2 protocol) to v3. The v3 binary has no v2 crypto: it
//! relies on the Bash filters having decrypted the worktree, re-encrypts
//! that plaintext with v3, and keeps the user's selection by rewriting each
//! `filter=crypt` attribute rule to the `transcrypt` macro.
//!
//! Nothing is lost if it fails or is interrupted: the worktree plaintext is
//! never modified, the rewritten attribute files and hook are restored, and
//! the v2 configuration (including its password) is left in place until the
//! user has verified the result.

use std::{fs, os::unix::ffi::OsStrExt, path::Path};
use crate::{
    git::*,
    passphrase,
    setup::{init_with_rollback, Rollback},
    worktree::{find_protected, indexed_path, staging_dir, write_repository_file},
    Options,
};

/// Whether an attribute token belongs to Bash transcrypt: `filter`, `diff`
/// or `merge` set to `crypt` or `crypt-<context>`.
fn v2_token(token: &[u8]) -> bool {
    [&b"filter="[..], b"diff=", b"merge="].iter().any(|key| token.strip_prefix(*key)
        .is_some_and(|value| value == b"crypt" || value.starts_with(b"crypt-")))
}

/// Split an attribute line into its pattern and the rest. A pattern that
/// starts with `"` is C-quoted (it may contain blanks) and ends at the
/// closing unescaped quote; otherwise it ends at the first blank.
fn split_pattern(line: &[u8]) -> (&[u8], &[u8]) {
    let start = line.len() - line.trim_ascii_start().len();
    let body = &line[start..];
    let end = if body.starts_with(b"\"") {
        let mut i = 1;
        while i < body.len() && body[i] != b'"' {
            i += if body[i] == b'\\' { 2 } else { 1 };
        }
        (i + 1).min(body.len())
    } else {
        body.iter().position(|b| b.is_ascii_whitespace()).unwrap_or(body.len())
    };
    (&line[..start + end], &body[end..])
}

/// Rewrite one `.gitattributes` text: every rule with v2 tokens keeps its
/// pattern and other attributes and gets `transcrypt` instead. Returns the
/// new text if anything changed.
fn rewrite_attributes(text: &[u8]) -> Option<Vec<u8>> {
    let mut changed = false;
    let lines: Vec<Vec<u8>> = text.split(|b| *b == b'\n').map(|line| {
        if line.trim_ascii_start().starts_with(b"#") { return line.to_vec(); }
        let (pattern, rest) = split_pattern(line);
        let tokens: Vec<&[u8]> = rest.split(|b| b.is_ascii_whitespace()).filter(|t| !t.is_empty()).collect();
        if !tokens.iter().any(|t| v2_token(t)) { return line.to_vec(); }
        changed = true;
        let mut out = pattern.to_vec();
        for token in tokens.into_iter().filter(|t| !v2_token(t)) {
            out.push(b' ');
            out.extend_from_slice(token);
        }
        out.extend_from_slice(b" transcrypt");
        out
    }).collect();
    changed.then(|| lines.join(&b'\n'))
}

/// `migrate`: see the module documentation.
pub(crate) fn migrate(root: &Path, options: &Options) -> Result<(), String> {
    // An uncommitted v3 config is an interrupted migration: rerunning it,
    // with the same v3 passphrase, completes it.
    let resuming = fs::symlink_metadata(root.join(".transcrypt")).is_ok();
    if resuming && git(root, &["cat-file", "-e", "HEAD:.transcrypt/config"]).is_ok() {
        return Err("this repository already uses v3".into());
    }
    if git(root, &["config", "--get", "filter.crypt.clean"]).is_err() {
        return Err("Bash transcrypt is not set up in this checkout: install it and unlock with the v2 \
            password first (`transcrypt -c <cipher> -p <password>`), so the worktree holds plaintext".into());
    }
    // Rules outside the repository's own files cannot be converted for
    // everyone; files they select would silently stay unprotected.
    let info = common_dir(root).join("info/attributes");
    if fs::read(&info).is_ok_and(|text| text.split(|b| *b == b'\n')
        .any(|line| !line.trim_ascii_start().starts_with(b"#") && split_pattern(line).1
            .split(|b| b.is_ascii_whitespace()).any(v2_token))) {
        return Err(format!("{} has Bash transcrypt rules; move them to .gitattributes (and commit) \
            first, so that the conversion keeps them for everyone", info.display()));
    }
    // The files Bash protects, by its attributes.
    let entries = indexed_files(root)?;
    let paths: Vec<&[u8]> = entries.iter().map(|e| e.path.as_slice()).collect();
    let mut command = git_command(Some(root));
    command.args(["-c", "core.ignorecase=false", "check-attr", "-z", "--stdin", "filter"]);
    let mut request = Vec::new();
    for path in &paths {
        request.extend_from_slice(path);
        request.push(0);
    }
    let response = run_git_input(command, request)?;
    let fields: Vec<&[u8]> = response.split(|b| *b == 0).collect();
    let mut selected = Vec::new();
    for record in fields.chunks(3).filter(|r| r.len() == 3) {
        // When resuming, rules already converted select with transcrypt-v3.
        if record[2] == b"crypt" || record[2].starts_with(b"crypt-") || (resuming && record[2] == b"transcrypt-v3") {
            selected.push(record[0].to_vec());
        }
    }
    // A committed state, except for an interrupted migration's own changes.
    let status = git(root, &["status", "--porcelain", "-z", "--untracked-files=no"])?;
    for entry in status.split(|b| *b == 0).filter(|e| e.len() > 3) {
        let path = &entry[3..];
        let own = resuming && entry[0] != b'R' && (path == b".transcrypt/config" || path == b".gitattributes"
            || path.ends_with(b"/.gitattributes") || selected.iter().any(|p| p == path));
        if !own {
            return Err("commit or discard your changes first; the conversion must start from a committed state".into());
        }
    }
    for path in &selected {
        let name = String::from_utf8_lossy(path);
        let target = find_protected(root, &indexed_path(path)?)?
            .ok_or_else(|| format!("{name} is missing from the worktree"))?;
        if target.read()?.0.starts_with(b"U2FsdGVk") {
            return Err(format!("{name} still holds v2 ciphertext: unlock it with Bash transcrypt first"));
        }
    }
    // Every refusal and the passphrase prompt come before any change, and
    // the steps are ordered so that an interruption at any point leaves a
    // state that still encrypts (Bash's rules or v3's) or that the v3 hook
    // refuses: set Bash's hook aside, set up v3, then rewrite the rules, then
    // re-encrypt.
    let attribute_files: Vec<std::path::PathBuf> = entries.iter()
        .filter(|e| e.path == b".gitattributes" || e.path.ends_with(b"/.gitattributes"))
        .map(|e| indexed_path(&e.path)).collect::<Result<_, _>>()?;
    let password = passphrase(options.password_stdin, true)?;
    // Bash's own pre-commit hook checks only `filter=crypt` files, which will
    // no longer exist; it is set aside so the v3 hook can be installed.
    let hooks = common_dir(root).join("hooks");
    let bash_hook = fs::read(hooks.join("pre-commit-crypt")).ok()
        .filter(|hook| fs::read(hooks.join("pre-commit")).ok().as_ref() == Some(hook));
    if bash_hook.is_some() {
        fs::rename(hooks.join("pre-commit"), hooks.join("pre-commit.transcrypt-v2"))
            .map_err(|e| format!("cannot set aside the Bash pre-commit hook: {e}"))?;
    }
    let mut rewritten: Vec<(std::path::PathBuf, Vec<u8>)> = Vec::new();
    let undo = |rewritten: &[(std::path::PathBuf, Vec<u8>)]| {
        if let Ok(staging) = staging_dir(root) {
            for (relative, original) in rewritten {
                let _ = write_repository_file(root, &staging, relative, original);
            }
        }
        if bash_hook.is_some() {
            let _ = fs::rename(hooks.join("pre-commit.transcrypt-v2"), hooks.join("pre-commit"));
        }
        let _ = git(root, &["reset", "-q", "--", "."]);
    };
    let rollback: Rollback = match init_with_rollback(root, options, Some(password)) {
        Ok(rollback) => rollback,
        Err(e) => { undo(&rewritten); return Err(format!("{e}; the conversion was rolled back")); },
    };
    let result = (|| -> Result<(), String> {
        // Rewrite every tracked .gitattributes that has v2 rules (the
        // top-level one now also defines the `transcrypt` macro).
        let staging = staging_dir(root)?;
        for relative in &attribute_files {
            let Some(file) = find_protected(root, relative)? else { continue };
            let original = file.read()?.0.to_vec();
            if let Some(text) = rewrite_attributes(&original) {
                write_repository_file(root, &staging, relative, &text)?;
                rewritten.push((relative.clone(), original));
            }
        }
        drop(staging);
        // Stage the rewritten attribute files and re-clean the decrypted
        // worktree files with the v3 filter (raw path bytes, no pathspec
        // magic: GIT_LITERAL_PATHSPECS).
        let mut paths = Vec::new();
        for path in rewritten.iter().map(|(p, _)| p.as_os_str().as_bytes()).chain(selected.iter().map(Vec::as_slice)) {
            paths.extend_from_slice(path);
            paths.push(0);
        }
        git_with_input(root, &["add", "--renormalize", "--pathspec-from-file=-", "--pathspec-file-nul"], &paths)?;
        // Every file v2 protected must now be protected by v3.
        let refs: Vec<&[u8]> = selected.iter().map(Vec::as_slice).collect();
        if let Some((path, _)) = refs.iter().zip(protected_flags(root, &refs, Attributes::Staged)?).find(|(_, p)| !*p) {
            return Err(format!("{} would no longer be protected after the conversion (an attribute \
                rule could not be converted); convert it in .gitattributes by hand", String::from_utf8_lossy(path)));
        }
        // Nothing may stay v2 ciphertext (a rule Git applied only
        // case-insensitively, or one that could not be converted).
        for entry in indexed_files(root)? {
            if git_blob_if_record_sized(root, &entry.oid)?.is_some_and(|b| b.starts_with(b"U2FsdGVk")) {
                return Err(format!("{} is still v2 ciphertext after the conversion (selected by a rule v3 \
                    does not apply, e.g. only case-insensitively); fix its rule in .gitattributes and rerun",
                    String::from_utf8_lossy(&entry.path)));
            }
        }
        crate::lifecycle::verify_index_command(root)
    })();
    if let Err(e) = result {
        rollback.run();
        undo(&rewritten);
        return Err(format!("{e}; the conversion was rolled back"));
    }
    eprintln!("Converted {} file(s) from Bash transcrypt to v3; review and commit:\n  \
        git commit -m 'Convert to transcrypt-v3'\n\
        Then clone the repository afresh and check that `transcrypt-v3 unlock` decrypts it. Only then \
        remove the v2 password from .git/config (`git config --remove-section transcrypt`).\n\
        Earlier commits keep their v2 ciphertext, readable with the v2 password: if that password \
        or the history was ever exposed, change the secrets themselves.", selected.len());
    if bash_hook.is_some() {
        eprintln!("The Bash pre-commit hook was renamed to .git/hooks/pre-commit.transcrypt-v2.");
    }
    Ok(())
}

/// Run a Git command with input; its output.
fn run_git_input(command: std::process::Command, input: Vec<u8>) -> Result<Vec<u8>, String> {
    let (status, out, errors) = run_bounded_status(command, Some(input), 256 << 20)?;
    if !status.success() {
        return Err(format!("git check-attr failed: {}", String::from_utf8_lossy(&errors)));
    }
    Ok(out.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v2_rules_become_the_transcrypt_macro() {
        let text = b"# comment filter=crypt\n*.key  filter=crypt diff=crypt merge=crypt\nsecret/** filter=crypt-ops diff=crypt-ops merge=crypt-ops -text\n*.png binary\n";
        let out = rewrite_attributes(text).unwrap();
        assert_eq!(out, b"# comment filter=crypt\n*.key transcrypt\nsecret/** -text transcrypt\n*.png binary\n");
        let quoted = b"\"my secret.txt\" filter=crypt diff=crypt merge=crypt\n\"a\\\"b c\" filter=crypt\n";
        assert_eq!(rewrite_attributes(quoted).unwrap(), b"\"my secret.txt\" transcrypt\n\"a\\\"b c\" transcrypt\n");
        assert_eq!(rewrite_attributes(b"*.png binary\n"), None);
        assert!(!v2_token(b"filter=cryptic") && v2_token(b"merge=crypt-a"));
    }
}
