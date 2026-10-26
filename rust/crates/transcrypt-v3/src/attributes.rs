//! The `.gitattributes` policy: the committed `transcrypt` macro, the
//! `protect` and `unprotect` commands that edit it, and the local attribute
//! files that could override it.

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
};
use std::os::unix::ffi::OsStrExt;
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
const MACRO_COMMENT: &[u8] = b"# transcrypt-v3: files matching a pattern marked `transcrypt` are encrypted in Git";
/// The top-level `.gitattributes` in the worktree, if any.
pub(crate) fn worktree_attributes(root: &Path) -> Result<Option<Vec<u8>>, String> {
    find_protected(root, Path::new(".gitattributes"))?.map(|f| f.read().map(|(bytes, _)| bytes.to_vec())).transpose()
}

/// Put the worktree's top-level `.gitattributes` back as `before` (`None`:
/// there was none); best effort.
pub(crate) fn restore_worktree_attributes(root: &Path, before: Option<&[u8]>) {
    match before {
        Some(bytes) => if let Ok(staging) = staging_dir(root) {
            let _ = write_repository_file(root, &staging, Path::new(".gitattributes"), bytes);
        },
        None => { let _ = fs::remove_file(root.join(".gitattributes")); },
    }
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
            worktree: worktree_attributes(root)?,
            staged: indexed_files(root)?.into_iter().find(|e| e.path == b".gitattributes").map(|e| (e.mode, e.oid)),
        })
    }

    fn restore(&self, root: &Path) {
        restore_worktree_attributes(root, self.worktree.as_deref());
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
fn check_pattern(root: &Path, submodules: &[Vec<u8>], pattern: &[u8]) -> Result<Vec<u8>, String> {
    let shown = String::from_utf8_lossy(pattern).into_owned();
    let mut pattern = pattern;
    while let Some(rest) = pattern.strip_prefix(b"./") { pattern = rest; }
    // A submodule never reads this repository's attributes.
    if let Some(sub) = submodules.iter().find(|sub| pattern.strip_prefix(sub.as_slice())
        .is_some_and(|rest| rest.is_empty() || rest.starts_with(b"/"))) {
        return Err(format!("{shown} is inside the submodule {}, which does not read this repository's \
            .gitattributes; run `transcrypt-v3 init`/`protect` inside the submodule", String::from_utf8_lossy(sub)));
    }
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

/// The key, and the checked patterns with their `.gitattributes` lines.
type Checked = (Key, Vec<Vec<u8>>, Vec<Line>);

/// The key, and each of `patterns` checked, with its `.gitattributes` line.
fn checked_patterns(root: &Path, patterns: &[OsString]) -> Result<Checked, String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let submodules: Vec<Vec<u8>> = indexed_files(root)?.into_iter().filter(|e| e.mode == "160000").map(|e| e.path).collect();
    let patterns = patterns.iter().map(|p| check_pattern(root, &submodules, p.as_bytes())).collect::<Result<Vec<_>, _>>()?;
    let lines = patterns.iter().map(|p| protect_line(p)).collect::<Result<_, _>>()?;
    Ok((key, patterns, lines))
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

/// The error for a missing macro.
pub(crate) const MACRO_MISSING: &str = "the `transcrypt` macro does not set filter=transcrypt-v3 here (the \
    top-level .gitattributes lost its `[attr]transcrypt` line, or another rule redefines or overrides it), \
    so files marked `transcrypt` would be stored unencrypted; restore the line (`transcrypt-v3 protect` \
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
pub(crate) fn edit_attributes(root: &Path, staging: &Staging, stage: bool, edit: impl FnOnce(&mut Vec<Line>) -> Result<(), String>)
    -> Result<(), String>
{
    let existing = worktree_attributes(root)?.unwrap_or_default();
    let mut lines: Vec<Line> = existing.split(|b| *b == b'\n').map(<[u8]>::to_vec).collect();
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
    if !stage { return Ok(()); }
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
    let (key, patterns, lines) = checked_patterns(root, patterns)?;
    let undo = AttributesUndo::capture(root)?;
    let result = (|| -> Result<(), String> {
        let staging = staging_dir(root)?;
        edit_attributes(root, &staging, true, |existing| {
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
    let (key, _, lines) = checked_patterns(root, patterns)?;
    let before = staged_protected(root, indexed_files(root)?)?;
    let undo = AttributesUndo::capture(root)?;
    let result = (|| -> Result<Vec<Vec<u8>>, String> {
        let staging = staging_dir(root)?;
        // The staged rules: an interrupted `unprotect` already removed the
        // line from the worktree file but not from the index.
        let staged_rules = undo.staged.as_ref().map(|(_, oid)| git_blob(root, oid)).transpose()?.unwrap_or_default();
        edit_attributes(root, &staging, false, |existing| {
            for line in &lines {
                let n = existing.len();
                existing.retain(|l| l != line);
                if existing.len() == n && !staged_rules.split(|b| *b == b'\n').any(|l| l.trim_ascii() == line.as_slice()) {
                    return Err(format!("no `{}` line in .gitattributes; edit it directly to change other rules",
                        String::from_utf8_lossy(line)));
                }
            }
            Ok(())
        })?;
        // The new rules are in the worktree only; the index (rules included)
        // changes in one update at the end, so an interruption never leaves
        // the rule removed while the records are still staged.
        let still = protected_flags(root, &paths_of(&before), Attributes::Worktree)?;
        // Decrypt everything before changing any file or index entry.
        let mut released = Vec::new();
        for (staged, _) in before.iter().zip(still).filter(|(_, still)| !still) {
            let plaintext = open_staged(root, &key, staged)?;
            released.push((staged, plaintext));
        }
        // A worktree file that still holds the record gets its plaintext
        // (harmless if a later step fails); the index changes last.
        for (staged, plaintext) in &released {
            replace_if_holds(root, &staging, &staged.path, &git_blob(root, &staged.oid)?, plaintext, key.private())?;
        }
        let mut index_info = Vec::new();
        for (staged, plaintext) in &released {
            push_blob_record(root, &mut index_info, &staged.mode, &staged.path, plaintext)?;
        }
        let rules = worktree_attributes(root)?.ok_or("missing .gitattributes")?;
        push_blob_record(root, &mut index_info, "100644", b".gitattributes", &rules)?;
        git_with_input(root, &["update-index", "-z", "--add", "--index-info"], &index_info)?;
        Ok(released.into_iter().map(|(staged, _)| staged.path.clone()).collect())
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

