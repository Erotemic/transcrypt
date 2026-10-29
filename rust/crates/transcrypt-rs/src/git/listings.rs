//! The index's and trees' listings, rewritten to one record shape and parsed
//! by the verified core, and what a commit changes.

use super::*;

/// Whether `path` is a `.gitattributes` file (at the top or nested).
pub(crate) fn is_attributes_file(path: &[u8]) -> bool {
    path == ATTRIBUTES_NAME || path.ends_with(&ATTRIBUTES_SUFFIX)
}

/// The non-empty NUL-separated records of Git `-z` output.
pub(crate) fn records(data: &[u8]) -> impl Iterator<Item = &[u8]> {
    data.split(|b| *b == 0).filter(|record| !record.is_empty())
}

/// `records` of a listing that must end with its last record's NUL.
fn complete_records(data: &[u8]) -> Result<impl Iterator<Item = &[u8]>, String> {
    if !data.is_empty() && data.last() != Some(&0) {
        return Err("truncated Git listing".into());
    }
    Ok(records(data))
}

/// The exact index listing (`ls-files --stage -z`), unmerged stages included.
pub(crate) fn index_listing(root: &Path) -> Result<Vec<u8>, String> {
    git(root, &["ls-files", "--stage", "-z"])
}

/// One `<mode> SP <oid> SP 0 TAB <path>` record (see `Listing`).
fn parse_entry(entry: &[u8]) -> Result<Staged, String> {
    let parsed = parse_index_entry(entry)
        .map_err(|_| "malformed or unmerged Git index entry; resolve conflicts first")?;
    let oid = &entry[OID_START..parsed.path_start - STAGE_ZERO_FIELD.len()];
    if !is_object_id(oid) {
        return Err("malformed Git object id in index entry".into());
    }
    Staged::new(parsed.regular, &entry[..MODE_LEN], oid, &entry[parsed.path_start..])
}

/// The blobs of a commit's tree.
pub(crate) fn tree_files(root: &Path, commit: &str) -> Result<Vec<Staged>, String> {
    Ok(tree_listing(root, commit)?.into_entries())
}

/// `tree_files`, as a `Listing`.
pub(crate) fn tree_listing(root: &Path, commit: &str) -> Result<Listing, String> {
    Listing::parse(tree_listing_bytes(root, &["ls-tree", "-r", "-z", "--full-tree", commit])?)
}

/// An `ls-tree -z` listing rewritten to index records. `ls-tree` prints
/// `<mode> SP <type> SP <oid> TAB <path>` (every Git version; `--format`
/// needs 2.36); each record is rewritten as `<mode> SP <oid> SP 0 TAB
/// <path>`, with the path copied verbatim, so that the verified core parses
/// and checks the listing exactly like an index listing.
fn tree_listing_bytes(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    for entry in records(&git(root, arguments)?) {
        bytes.extend_from_slice(&tree_record(entry)?);
        bytes.push(0);
    }
    Ok(bytes)
}

/// Rewrite one `ls-tree` record as `<mode> SP <oid> SP 0 TAB <path>`.
pub(super) fn tree_record(entry: &[u8]) -> Result<Vec<u8>, String> {
    let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed git ls-tree record")?;
    let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
    let [mode, _kind, oid] = fields[..] else { return Err("malformed git ls-tree record".into()) };
    Ok([mode, b" ", oid, STAGE_ZERO_FIELD, &entry[tab + 1..]].concat())
}

/// The index during a merge: its exact listing, the stage-0 entries (parsed
/// by the verified core) and, once each, the paths of unmerged entries
/// (`<mode> SP <oid> SP <1|2|3> TAB <path>`; Git lists stages of a path
/// together).
pub(crate) struct Index {
    pub(crate) listing: Vec<u8>,
    pub(crate) merged: Vec<Staged>,
    pub(crate) conflicted: Vec<Vec<u8>>,
}

pub(crate) fn index_with_conflicts(root: &Path) -> Result<Index, String> {
    let listing = index_listing(root)?;
    let mut merged = Vec::new();
    let mut conflicted: Vec<Vec<u8>> = Vec::new();
    for entry in complete_records(&listing)? {
        let tab = entry.iter().position(|b| *b == b'\t').ok_or("malformed Git index entry")?;
        if tab >= STAGE_FIELD_LEN && entry[tab - STAGE_FIELD_LEN] == b' ' && CONFLICT_STAGES.contains(&entry[tab - 1]) {
            let path = entry[tab + 1..].to_vec();
            if conflicted.last() != Some(&path) { conflicted.push(path); }
        } else {
            merged.push(parse_entry(entry)?);
        }
    }
    Ok(Index { merged, listing, conflicted })
}

/// The stage-0 entries of the index (`Listing::parse`).
pub(crate) fn indexed_files(root: &Path) -> Result<Vec<Staged>, String> {
    Ok(Listing::parse(index_listing(root)?)?.into_entries())
}

/// The blobs Git already has for exactly `path`: every index stage, and
/// `HEAD`'s. Used to let a filter pass bytes through unchanged only when
/// they are one of these, never because of a header alone. A path that is
/// not UTF-8 (which cannot be passed as an argument on every OS) has none:
/// fail-closed, since the filter then never passes bytes through for it.
pub(crate) fn blobs_at(root: &Path, path: &[u8]) -> Result<Vec<String>, String> {
    let name = std::str::from_utf8(path).ok().map(str::to_owned);
    let mut oids = Vec::new();
    let mut parse = |listing: &[u8], tree: bool| {
        for entry in records(listing) {
            let Some(tab) = entry.iter().position(|b| *b == b'\t') else { continue };
            if &entry[tab + 1..] != path { continue; }
            let fields: Vec<&[u8]> = entry[..tab].split(|b| *b == b' ').collect();
            // `<mode> <oid> <stage>` (index) or `<mode> <type> <oid>` (tree).
            const INDEX_OID_FIELD: usize = 1;
            const TREE_OID_FIELD: usize = 2;
            let oid = fields.get(if tree { TREE_OID_FIELD } else { INDEX_OID_FIELD });
            if let Some(oid) = oid.filter(|o| is_object_id(o)) {
                oids.push(String::from_utf8_lossy(oid).into_owned());
            }
        }
    };
    let Some(name) = name else { return Ok(oids) };
    parse(&git(root, &["ls-files", "--stage", "-z", "--", &name])?, false);
    if let Ok(listing) = git(root, &["ls-tree", "-z", "HEAD", "--", &name]) { parse(&listing, true); }
    Ok(oids)
}

/// A path and the blob it holds (or held).
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct PathBlob {
    pub(crate) path: Vec<u8>,
    pub(crate) oid: String,
}

/// What a commit changes relative to its parent.
pub(crate) struct Changes {
    /// The entries it adds or changes, as they are in the commit.
    pub(crate) entries: Vec<Staged>,
    /// The paths it deletes, with their old blobs.
    pub(crate) deleted: Vec<PathBlob>,
    /// The paths it modifies, with their old blobs.
    pub(crate) modified: Vec<PathBlob>,
}

/// The entries a commit adds or changes relative to `parent` (all of its
/// entries for a root commit), from `diff-tree -r -z --raw` between the two
/// trees, rewritten to the index-record shape and parsed by the verified
/// core, and the paths it deletes with their old object ids.
pub(crate) fn changed_files(root: &Path, commit: &str, parent: Option<&str>) -> Result<Changes, String> {
    let Some(parent) = parent else {
        return Ok(Changes { entries: tree_files(root, commit)?, deleted: Vec::new(), modified: Vec::new() });
    };
    let data = git(root, &["diff-tree", "-r", "-z", "--raw", "--no-renames", "--no-abbrev", parent, commit])?;
    parse_diff_tree(&data)
}

/// Parse `diff-tree -r -z --raw` records,
/// `:<old mode> <new mode> <old oid> <new oid> <status> NUL <path> NUL`, keeping
/// the new side of every entry that is not deleted, and the deleted paths
/// with their old object ids.
pub(super) fn parse_diff_tree(data: &[u8]) -> Result<Changes, String> {
    if !data.is_empty() && data.last() != Some(&0) {
        return Err("truncated git diff-tree output".into());
    }
    let mut fields = data.split(|b| *b == 0);
    let mut entries = Vec::new();
    let mut deleted = Vec::new();
    let mut modified = Vec::new();
    while let Some(header) = fields.next() {
        if header.is_empty() { break; }
        let path = fields.next().ok_or("malformed git diff-tree output")?;
        let parts: Vec<&[u8]> = header.strip_prefix(b":").ok_or("malformed git diff-tree output")?
            .split(|b| *b == b' ').collect();
        let [_, mode, old, oid, status] = parts[..] else { return Err("malformed git diff-tree output".into()) };
        let old = || -> Result<_, String> {
            if !is_object_id(old) { return Err("malformed git diff-tree output".into()); }
            Ok(PathBlob { path: path.to_vec(), oid: String::from_utf8_lossy(old).into_owned() })
        };
        match status {
            b"D" => { deleted.push(old()?); continue },
            b"A" => {},
            b"M" | b"T" => modified.push(old()?),
            _ => return Err("unexpected git diff-tree status".into()),
        }
        entries.push(parse_entry(&[mode, b" ", oid, b" 0\t", path].concat())?);
    }
    Ok(Changes { entries, deleted, modified })
}

/// The `.transcrypt/config` blob of a commit, if it has one.
pub(crate) fn config_blob(root: &Path, commit: &str) -> Result<Option<String>, String> {
    let listing = tree_listing_bytes(root, &["ls-tree", "-z", "--full-tree", commit, "--", CONFIG_PATH])?;
    Ok(Listing::parse(listing)?.into_entries().into_iter()
        .find(|e| e.path == CONFIG_PATH.as_bytes() && e.regular).map(|e| e.oid))
}

/// Re-index exactly `paths`, whose worktree content cleans to the staged
/// blob, and check that no staged blob or mode changed from `listing`.
pub(crate) fn reindex(root: &Path, listing: &[u8], paths: &[Vec<u8>]) -> Result<(), String> {
    if paths.is_empty() { return Ok(()); }
    git_with_input(root, &["update-index", "-z", "--stdin"], &nul_terminated(paths))?;
    if index_listing(root)? != listing {
        return Err("staged Git objects changed while refreshing the index; inspect `git diff --cached`".into());
    }
    Ok(())
}
