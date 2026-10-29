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

use std::{fs, path::{Path, PathBuf}};
use crate::{
    attributes::split_lines,
    git::*,
    passphrase,
    setup::{init_with_rollback, uncommitted_setup},
    worktree::{find_protected, indexed_path, staging_dir, write_repository_file},
    Options,
};

/// How a Bash transcrypt (v2) record starts: OpenSSL's `Salted__`, in
/// base64.
const V2_CIPHERTEXT: &[u8] = b"U2FsdGVk";

/// A Bash transcrypt driver name: `crypt` or `crypt-<context>`.
fn v2_value(value: &[u8]) -> bool {
    value == b"crypt" || value.starts_with(b"crypt-")
}

/// Whether an attribute token belongs to Bash transcrypt: `filter`, `diff`
/// or `merge` set to a v2 driver.
fn v2_token(token: &[u8]) -> bool {
    [&b"filter="[..], b"diff=", b"merge="].iter().any(|key| token.strip_prefix(*key).is_some_and(v2_value))
}

/// Whether an attribute line (not a comment) has a Bash transcrypt token.
fn v2_rule(line: &[u8]) -> bool {
    !line.trim_ascii_start().starts_with(b"#")
        && split_pattern(line).1.split(u8::is_ascii_whitespace).any(v2_token)
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
    if !split_lines(text).any(v2_rule) { return None; }
    let lines: Vec<Vec<u8>> = split_lines(text).map(|line| {
        if !v2_rule(line) { return line.to_vec(); }
        let (pattern, rest) = split_pattern(line);
        let mut out = pattern.to_vec();
        for token in rest.split(u8::is_ascii_whitespace).filter(|t| !t.is_empty() && !v2_token(t)) {
            out.push(b' ');
            out.extend_from_slice(token);
        }
        out.extend_from_slice(b" transcrypt");
        out
    }).collect();
    Some(lines.join(&b'\n'))
}

/// `migrate`: see the module documentation.
pub(crate) fn migrate(root: &Path, options: &Options) -> Result<(), String> {
    // An uncommitted v3 config is an interrupted migration: rerunning it,
    // with the same v3 passphrase, completes it.
    let resuming = uncommitted_setup(root, "this repository already uses v3")?;
    if git(root, &["config", "--get", "filter.crypt.clean"]).is_err() {
        return Err("Bash transcrypt is not set up in this checkout: install it and unlock with the v2 \
            password first (`transcrypt -c <cipher> -p <password>`), so the worktree holds plaintext".into());
    }
    // Rules outside the repository's own files cannot be converted for
    // everyone; files they select would silently stay unprotected.
    let info = common_dir(root).join("info/attributes");
    if fs::read(&info).is_ok_and(|text| split_lines(&text).any(v2_rule)) {
        return Err(format!("{} has Bash transcrypt rules; move them to .gitattributes (and commit) \
            first, so that the conversion keeps them for everyone", info.display()));
    }
    // The files Bash protects, by its attributes.
    let entries = indexed_files(root)?;
    let paths = paths_of(&entries);
    // When resuming, rules already converted select with transcrypt-v3.
    let selected: Vec<&[u8]> = paths.iter().zip(filter_values(root, &paths, Attributes::Worktree)?)
        .filter(|(_, value)| v2_value(value) || (resuming && value == b"transcrypt-v3"))
        .map(|(path, _)| *path).collect();
    // A committed state, except for an interrupted migration's own changes.
    let status = git(root, &["status", "--porcelain", "-z", "--untracked-files=no"])?;
    for entry in status.split(|b| *b == 0).filter(|e| e.len() > 3) {
        let path = &entry[3..];
        let own = resuming && entry[0] != b'R'
            && (path == CONFIG_PATH.as_bytes() || is_attributes_file(path) || selected.contains(&path));
        if !own {
            return Err("commit or discard your changes first; the conversion must start from a committed state".into());
        }
    }
    for path in &selected {
        let name = String::from_utf8_lossy(path);
        let target = find_protected(root, &indexed_path(path)?)?
            .ok_or_else(|| format!("{name} is missing from the worktree"))?;
        if target.read()?.0.starts_with(V2_CIPHERTEXT) {
            return Err(format!("{name} still holds v2 ciphertext: unlock it with Bash transcrypt first"));
        }
    }
    // Every refusal and the passphrase prompt come before any change, and
    // the steps are ordered so that an interruption at any point leaves a
    // state that still encrypts (Bash's rules or v3's) or that the v3 hook
    // refuses: set Bash's hook aside, set up v3, then rewrite the rules, then
    // re-encrypt.
    let attribute_files: Vec<PathBuf> = entries.iter()
        .filter(|e| is_attributes_file(&e.path))
        .map(|e| indexed_path(&e.path)).collect::<Result<_, _>>()?;
    let password = passphrase(options.password_stdin, true)?;
    // Bash's own pre-commit hook checks only `filter=crypt` files, which will
    // no longer exist; it is set aside so the v3 hook can be installed.
    let hooks = common_dir(root).join("hooks");
    let bash_hook = matches!((fs::read(hooks.join("pre-commit-crypt")), fs::read(hooks.join("pre-commit"))),
        (Ok(crypt), Ok(current)) if crypt == current);
    if bash_hook {
        fs::rename(hooks.join("pre-commit"), hooks.join("pre-commit.transcrypt-v2"))
            .map_err(|e| format!("cannot set aside the Bash pre-commit hook: {e}"))?;
    }
    // Put Bash's hook and the index back (the start was committed).
    let restore_bash = || {
        if bash_hook {
            let _ = fs::rename(hooks.join("pre-commit.transcrypt-v2"), hooks.join("pre-commit"));
        }
        let _ = git(root, &["reset", "-q", "--", "."]);
    };
    let rollback = match init_with_rollback(root, options, Some(password)) {
        Ok(rollback) => rollback,
        Err(e) if resuming => return Err(format!("{e}; rerun `transcrypt-rs migrate` to complete the conversion")),
        Err(e) => { restore_bash(); return Err(format!("{e}; the conversion was rolled back")); },
    };
    let mut rewritten = Vec::new();
    if let Err(e) = convert(root, &attribute_files, &selected, &mut rewritten) {
        // Undo this run's rewrites first: a resumed run stays resumable, and
        // the rollback then restores the top-level file from before `init`.
        if let Ok(staging) = staging_dir(root) {
            for (relative, original) in &rewritten {
                let _ = write_repository_file(root, &staging, relative, original);
            }
        }
        if resuming {
            return Err(format!("{e}; fix that, then rerun `transcrypt-rs migrate` to complete the conversion"));
        }
        rollback.run();
        restore_bash();
        return Err(format!("{e}; the conversion was rolled back"));
    }
    eprintln!("Converted {} file(s) from Bash transcrypt to v3; review and commit:\n  \
        git commit -m 'Convert to transcrypt-v3'\n\
        Then clone the repository afresh and check that `transcrypt-rs unlock` decrypts it. Only then \
        remove the v2 password from .git/config (`git config --remove-section transcrypt`).\n\
        Earlier commits keep their v2 ciphertext, readable with the v2 password: if that password \
        or the history was ever exposed, change the secrets themselves.", selected.len());
    if bash_hook {
        eprintln!("The Bash pre-commit hook was renamed to .git/hooks/pre-commit.transcrypt-v2.");
    }
    Ok(())
}

/// Rewrite every tracked `.gitattributes` that has v2 rules (the top-level
/// one now also defines the `transcrypt` macro), recording each original in
/// `rewritten`; re-encrypt the selected files; and check that v3 protects
/// all of them.
fn convert(root: &Path, attribute_files: &[PathBuf], selected: &[&[u8]], rewritten: &mut Vec<(PathBuf, Vec<u8>)>)
    -> Result<(), String>
{
    let staging = staging_dir(root)?;
    for relative in attribute_files {
        let Some(file) = find_protected(root, relative)? else { continue };
        let original = file.read()?.0.to_vec();
        if let Some(text) = rewrite_attributes(&original) {
            write_repository_file(root, &staging, relative, &text)?;
            rewritten.push((relative.clone(), original));
        }
    }
    drop(staging);
    // Stage the rewritten attribute files and re-clean the decrypted worktree
    // files with the v3 filter. `--renormalize` (which `update-index` lacks)
    // needs `git add`; the paths are raw bytes and literal
    // (GIT_LITERAL_PATHSPECS), so no pathspec magic applies.
    let paths: Vec<&[u8]> = rewritten.iter().map(|(p, _)| crate::os::os_bytes(p.as_os_str())).chain(selected.iter().copied()).collect();
    git_with_input(root, &["add", "--renormalize", "--pathspec-from-file=-", "--pathspec-file-nul"], &nul_terminated(&paths))?;
    // Every file v2 protected must now be protected by v3.
    if let Some((path, _)) = selected.iter().zip(protected_flags(root, selected, Attributes::Staged)?).find(|(_, p)| !*p) {
        return Err(format!("{} would no longer be protected after the conversion (an attribute \
            rule could not be converted); convert it in .gitattributes by hand", String::from_utf8_lossy(path)));
    }
    // Nothing may stay v2 ciphertext (a rule Git applied only
    // case-insensitively, or one that could not be converted).
    for entry in indexed_files(root)? {
        if git_blob_if_record_sized(root, &entry.oid)?.is_some_and(|b| b.starts_with(V2_CIPHERTEXT)) {
            return Err(format!("{} is still v2 ciphertext after the conversion (selected by a rule v3 \
                does not apply, e.g. only case-insensitively); fix its rule in .gitattributes and rerun",
                entry.name()));
        }
    }
    crate::lifecycle::verify_index_command(root)
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
