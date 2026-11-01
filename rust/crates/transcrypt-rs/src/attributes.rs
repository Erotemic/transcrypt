//! The `.gitattributes` policy: the committed `transcrypt` macro, the
//! `protect` and `unprotect` commands that edit it, and the local attribute
//! files that could override it.

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
};
use transcrypt_v3_core::FILTER_ATTR;
use crate::{
    credential::Key,
    git::*,
    lifecycle::*,
    load_config,
    worktree::{find_protected, replace_if_holds, staging_dir, write_repository_file, Staging},
};

/// The committed attribute macro: a pattern followed by `transcrypt` is
/// encrypted (`filter`), diffed and merged decrypted (`diff`, `merge`, local
/// drivers; a checkout without them sees binary files), and never
/// line-ending converted (`-text`: Git would convert the ciphertext).
pub(crate) const MACRO: &[u8] = b"[attr]transcrypt filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text";
/// ASCII DEL, a control character Git's quoting escapes.
const DEL: u8 = 0x7f;
/// Digits of a C-style octal escape (`\ooo`) of one byte.
const OCTAL_ESCAPE_DIGITS: usize = 3;
const MACRO_COMMENT: &[u8] = b"# transcrypt-v3: files matching a pattern marked `transcrypt` are encrypted in Git";
/// The top-level `.gitattributes` in the worktree, if any.
pub(crate) fn worktree_attributes(repo: &Repository) -> Result<Option<Vec<u8>>, String> {
    find_protected(repo.root(), Path::new(".gitattributes"))?.map(|f| f.read().map(|(bytes, _)| bytes.to_vec())).transpose()
}

/// Put the worktree's top-level `.gitattributes` back as `before` (`None`:
/// there was none); best effort.
pub(crate) fn restore_worktree_attributes(repo: &Repository, before: Option<&[u8]>) {
    match before {
        Some(bytes) => if let Ok(staging) = staging_dir(repo) {
            let _ = write_repository_file(repo.root(), &staging, Path::new(".gitattributes"), bytes);
        },
        None => { let _ = fs::remove_file(repo.root().join(".gitattributes")); },
    }
}

/// The top-level `.gitattributes` as it was, in the worktree and the index,
/// so that a command that fails after editing it can put both back.
struct AttributesUndo {
    worktree: Option<Vec<u8>>,
    staged: Option<(String, String)>,
}

impl AttributesUndo {
    fn capture(repo: &Repository) -> Result<AttributesUndo, String> {
        Ok(AttributesUndo {
            worktree: worktree_attributes(repo)?,
            staged: indexed_files(repo)?.into_iter().find(|e| e.path == b".gitattributes").map(|e| (e.mode().to_owned(), e.oid)),
        })
    }

    fn restore(&self, repo: &Repository) {
        restore_worktree_attributes(repo, self.worktree.as_deref());
        let _ = match &self.staged {
            Some((mode, oid)) => git_with_input(repo, &["update-index", "-z", "--index-info"],
                format!("{mode} {oid}\t.gitattributes\0").as_bytes()),
            None => git(repo, &["update-index", "--force-remove", "--", ".gitattributes"]),
        };
    }

    /// Run `edit` with `.gitattributes` captured, putting it back if `edit` fails.
    fn guard<T>(repo: &Repository, edit: impl FnOnce(&AttributesUndo) -> Result<T, String>) -> Result<T, String> {
        let undo = AttributesUndo::capture(repo)?;
        let result = edit(&undo);
        if result.is_err() { undo.restore(repo); }
        result
    }
}

/// The pieces of `text` between line feeds (the last is empty after a
/// final newline).
pub(crate) fn split_lines(text: &[u8]) -> impl Iterator<Item = &[u8]> {
    text.split(|b| *b == b'\n')
}

/// The paths of `entries`, owned (`paths_of` borrows them).
pub(crate) fn owned_paths(entries: &[Staged]) -> Vec<Vec<u8>> {
    entries.iter().map(|e| e.path.clone()).collect()
}

/// Patterns as the user wrote them must select what they name. Git applies
/// `.gitattributes` patterns to files only, relative to the top-level
/// directory, without `./`, and has no negation: refuse what would silently
/// select nothing.
fn check_pattern(repo: &Repository, submodules: &[Vec<u8>], pattern: &[u8]) -> Result<Vec<u8>, String> {
    let shown = String::from_utf8_lossy(pattern).into_owned();
    let mut pattern = pattern;
    while let Some(rest) = pattern.strip_prefix(b"./") { pattern = rest; }
    // A submodule never reads this repository's attributes.
    if let Some(sub) = submodules.iter().find(|sub| pattern.strip_prefix(sub.as_slice())
        .is_some_and(|rest| rest.is_empty() || rest.starts_with(b"/"))) {
        return Err(format!("{shown} is inside the submodule {}, which does not read this repository's \
            .gitattributes; run `transcrypt-rs init`/`protect` inside the submodule", String::from_utf8_lossy(sub)));
    }
    if pattern.starts_with(b"!") {
        return Err(format!("{shown}: .gitattributes has no negative patterns; to exclude a file from a \
            protected pattern, add `PATH -filter -diff -merge` to .gitattributes"));
    }
    if pattern.ends_with(b"/") || repo.root().join(crate::os::os_string(pattern)?).is_dir() {
        let dir = String::from_utf8_lossy(pattern.strip_suffix(b"/").unwrap_or(pattern)).into_owned();
        return Err(format!("{shown}: attribute patterns select files, not directories; use '{dir}/**' \
            for everything below it"));
    }
    Ok(pattern.to_vec())
}

/// The patterns of `protect` or `unprotect`, checked, and the key.
struct Checked {
    key: Key,
    patterns: Vec<Vec<u8>>,
    /// The `.gitattributes` line of each pattern.
    lines: Vec<Line>,
}

/// The key, and each of `patterns` checked, with its `.gitattributes` line.
fn checked_patterns(repo: &Repository, patterns: &[OsString]) -> Result<Checked, String> {
    let config = load_config(repo)?;
    let key = Key::require(repo, &config)?;
    let submodules: Vec<Vec<u8>> = indexed_files(repo)?.into_iter().filter(|e| e.mode() == GITLINK_MODE).map(|e| e.path).collect();
    let patterns = patterns.iter().map(|p| check_pattern(repo, &submodules, crate::os::os_bytes(p))).collect::<Result<Vec<_>, _>>()?;
    let lines = patterns.iter().map(|p| protect_line(p)).collect::<Result<_, _>>()?;
    Ok(Checked { key, patterns, lines })
}

/// After `.gitattributes` was edited: a pattern that names an existing file
/// must select it (a backslash or bracket in a name is a glob character).
fn check_selects(repo: &Repository, patterns: &[Vec<u8>]) -> Result<(), String> {
    let files: Vec<&[u8]> = patterns.iter().map(Vec::as_slice)
        .filter(|p| crate::os::os_string(p).is_ok_and(|p| repo.root().join(p).is_file())).collect();
    for (path, protected) in files.iter().zip(protected_flags(repo, &files, Attributes::Worktree)?) {
        if !protected {
            return Err(format!("the pattern {} does not select the file of that name (Git reads `\\`, `*`, \
                `?` and `[` in patterns as glob characters); escape them, e.g. `[[]` for `[`",
                String::from_utf8_lossy(path)));
        }
    }
    Ok(())
}

/// The error for a missing macro.
pub(crate) const MACRO_MISSING: &str = "the `transcrypt` macro does not set filter=transcrypt-v3 here (the \
    top-level .gitattributes lost its `[attr]transcrypt` line, or another rule redefines or overrides it), \
    so files marked `transcrypt` would be stored unencrypted; restore the line (`transcrypt-rs protect` \
    with any of your patterns re-adds it) and remove the other definition";

/// Whether an attribute line defines the `transcrypt` macro.
fn defines_macro(line: &[u8]) -> bool {
    let line = line.trim_ascii();
    line.strip_prefix(b"[attr]transcrypt").or_else(|| line.strip_prefix(b"\"[attr]transcrypt\""))
        .is_some_and(|rest| rest.is_empty() || rest[0].is_ascii_whitespace())
}

/// One `.gitattributes` line, as bytes, without its newline.
type Line = Vec<u8>;

/// Rewrite the top-level `.gitattributes` through `edit` (after making
/// sure it defines the `transcrypt` macro), write it safely and stage it.
pub(crate) fn edit_attributes(repo: &Repository, staging: &Staging, stage: bool, edit: impl FnOnce(&mut Vec<Line>) -> Result<(), String>)
    -> Result<(), String>
{
    let existing = worktree_attributes(repo)?.unwrap_or_default();
    let mut lines: Vec<Line> = split_lines(&existing).map(<[u8]>::to_vec).collect();
    if lines.last().is_some_and(Vec::is_empty) { lines.pop(); }
    // Another definition of the macro would silently replace ours (Git uses
    // the last one), and `PATTERN transcrypt` would select nothing.
    if let Some(other) = lines.iter().find(|l| defines_macro(l) && l.trim_ascii() != MACRO) {
        return Err(format!(".gitattributes already defines the `transcrypt` macro differently (`{}`); \
            remove or rename that definition first", String::from_utf8_lossy(other)));
    }
    if !lines.iter().any(|l| l.trim_ascii() == MACRO) {
        // Macros may only be defined in the top-level file; put it first.
        lines.splice(0..0, [MACRO_COMMENT.to_vec(), MACRO.to_vec()]);
    }
    edit(&mut lines)?;
    let mut text = lines.join(&b'\n');
    text.push(b'\n');
    if text != existing {
        write_repository_file(repo.root(), staging, Path::new(".gitattributes"), &text)?;
        // Repository metadata must stay readable: refuse a pattern that
        // selects it (Git would then fail to stage .gitattributes itself).
        let reserved: [&[u8]; 3] = [b".gitattributes", CONFIG_PATH.as_bytes(), b".gitmodules"];
        let selected = protected_flags(repo, &reserved, Attributes::Worktree)?;
        if let Some((path, _)) = reserved.iter().zip(selected).find(|(_, p)| *p) {
            if existing.is_empty() {
                let _ = fs::remove_file(repo.root().join(".gitattributes"));
            } else {
                write_repository_file(repo.root(), staging, Path::new(".gitattributes"), &existing)?;
            }
            return Err(format!("that pattern would encrypt {}, which Git and v3 must read unencrypted; \
                use a narrower pattern", String::from_utf8_lossy(path)));
        }
    }
    if !stage { return Ok(()); }
    git(repo, &["add", "--", ".gitattributes"]).map(|_| ())
}

/// A `.gitattributes` line protecting `pattern`. Git reads a pattern that
/// starts with `"` as a C-style quoted string, so names with spaces, quotes,
/// backslashes or control characters are quoted.
fn protect_line(pattern: &[u8]) -> Result<Line, String> {
    if pattern.is_empty() || pattern.contains(&0) || pattern.starts_with(b"[attr]") || pattern.starts_with(b"#") {
        return Err(format!("invalid pattern {:?}", String::from_utf8_lossy(pattern)));
    }
    // Git ends an unquoted pattern at the first blank.
    let plain = !pattern.starts_with(b"\"") && pattern.iter().all(|b| *b > b' ' && *b != DEL);
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
                b if b < b' ' || b == DEL => line.extend_from_slice(format!("\\{b:0OCTAL_ESCAPE_DIGITS$o}").as_bytes()),
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
pub(crate) fn protect(repo: &Repository, patterns: &[OsString]) -> Result<(), String> {
    let Checked { key, patterns, lines } = checked_patterns(repo, patterns)?;
    AttributesUndo::guard(repo, |_| {
        let staging = staging_dir(repo)?;
        edit_attributes(repo, &staging, true, |existing| {
            for line in lines {
                if !existing.contains(&line) { existing.push(line); }
            }
            Ok(())
        })?;
        drop(staging);
        check_selects(repo, &patterns)?;
        // Seal every selected file still staged in plaintext: newly selected
        // ones, and ones a hand-edited `.gitattributes` selected earlier.
        let protected = staged_protected(repo, indexed_files(repo)?)?;
        let sealed = seal_staged(repo, &key, &owned_paths(&protected))?;
        match protected.len() {
            0 => eprintln!("Protected patterns added; no tracked file matches yet. `git add` encrypts matching files."),
            n => eprintln!("{n} tracked file(s) protected{}.",
                if sealed > 0 { format!("; {sealed} of them encrypted in the index just now") } else { String::new() }),
        }
        if sealed > 0 && git(repo, &["rev-parse", "-q", "--verify", "HEAD^{commit}"]).is_ok() {
            eprintln!("Files that were committed before they were protected stay readable in earlier commits: \
                if the history is public, change those secrets.");
        }
        Ok(())
    })
}

/// `unprotect PATTERN...`: remove the `PATTERN transcrypt` lines, and stage
/// the plaintext of each tracked file that is no longer protected (its next
/// commit publishes it unencrypted, which is the point). Every record to be
/// released is decrypted first; on any error `.gitattributes` and the index
/// are restored.
pub(crate) fn unprotect(repo: &Repository, patterns: &[OsString]) -> Result<(), String> {
    let Checked { key, lines, .. } = checked_patterns(repo, patterns)?;
    let before = staged_protected(repo, indexed_files(repo)?)?;
    let released = AttributesUndo::guard(repo, |undo| {
        let staging = staging_dir(repo)?;
        // The staged rules: an interrupted `unprotect` already removed the
        // line from the worktree file but not from the index.
        let staged_rules = undo.staged.as_ref().map(|(_, oid)| git_blob(repo, oid)).transpose()?.unwrap_or_default();
        edit_attributes(repo, &staging, false, |existing| {
            for line in &lines {
                let n = existing.len();
                existing.retain(|l| l != line);
                if existing.len() == n && !split_lines(&staged_rules).any(|l| l.trim_ascii() == line.as_slice()) {
                    return Err(format!("no `{}` line in .gitattributes; edit it directly to change other rules",
                        String::from_utf8_lossy(line)));
                }
            }
            Ok(())
        })?;
        // The new rules are in the worktree only; the index (rules included)
        // changes in one update at the end, so an interruption never leaves
        // the rule removed while the records are still staged.
        let still = protected_flags(repo, &paths_of(&before), Attributes::Worktree)?;
        // Decrypt everything before changing any file or index entry.
        let mut released = Vec::new();
        for (staged, _) in before.iter().zip(still).filter(|(_, still)| !still) {
            let plaintext = open_staged(repo, &key, staged)?;
            released.push((staged, plaintext));
        }
        // A worktree file that still holds the record gets its plaintext
        // (harmless if a later step fails); the index changes last.
        for (staged, plaintext) in &released {
            replace_if_holds(repo.root(), &staging, &staged.path, &git_blob(repo, &staged.oid)?, plaintext, key.private())?;
        }
        let mut update = IndexUpdate::new(repo, Blobs::Plaintext);
        for (staged, plaintext) in &released {
            update.add(staged.mode(), &staged.path, plaintext)?;
        }
        let rules = worktree_attributes(repo)?.ok_or("missing .gitattributes")?;
        update.add(REGULAR_FILE_MODE, b".gitattributes", &rules)?;
        update.apply(&["--add"])?;
        Ok(released.into_iter().map(|(staged, _)| staged.path.clone()).collect::<Vec<_>>())
    })?;
    eprintln!("{} file(s) are no longer protected; their next commit stores them UNENCRYPTED:", released.len());
    for path in &released {
        eprintln!("  {}", String::from_utf8_lossy(path));
    }
    Ok(())
}

/// The attribute files Git reads besides the repository's own
/// `.gitattributes`: `info/attributes` and `core.attributesFile` (by default
/// `$XDG_CONFIG_HOME/git/attributes`).
fn local_attribute_files(repo: &Repository) -> Vec<PathBuf> {
    let mut files = vec![repo.common_dir().join("info/attributes")];
    match git(repo, &["config", "--path", "core.attributesFile"]) {
        // Relative to the worktree root, where Git reads it from.
        Ok(path) => files.push(repo.root().join(String::from_utf8_lossy(&path).trim_end())),
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
pub(crate) fn filter_overrides(repo: &Repository) -> Vec<String> {
    local_attribute_files(repo).into_iter().filter(|file| fs::read(file)
        .is_ok_and(|text| split_lines(&text)
            .any(|line| line.windows(FILTER_ATTR.len()).any(|w| w == FILTER_ATTR) || defines_macro(line))))
        .map(|file| file.display().to_string()).collect()
}

