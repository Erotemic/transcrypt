//! Git's attribute answers (`check-attr`), parsed by the verified core.

use super::*;

/// Which attribute files Git consults to decide what is protected.
#[derive(Clone, Copy)]
pub(crate) enum Attributes<'a> {
    /// The staged `.gitattributes` files: what the next commit will say.
    Staged,
    /// The worktree's: what `git add` applies to a new file.
    Worktree,
    /// Those of a temporary index file (a commit's, for `audit`).
    Index(&'a Path),
}

/// `git check-attr -z --stdin <attributes>` for `paths`, sent as raw bytes
/// (any valid Unix name works), from the attribute files `from` selects.
/// Patterns match case-sensitively (`core.ignorecase=false`) so that every
/// clone, on every file system, selects the same files.
fn check_attr(root: &Path, paths: &[&[u8]], from: Attributes, attributes: &[&str]) -> Result<AttrAnswer, String> {
    if paths.iter().any(|path| path.is_empty() || path.contains(&0)) {
        return Err("invalid Git path".into());
    }
    let request = nul_terminated(paths);
    let mut command = git_command(Some(root));
    command.args(["-c", "core.ignorecase=false", "check-attr"]);
    match from {
        Attributes::Staged => { command.arg("--cached"); },
        Attributes::Worktree => {},
        Attributes::Index(file) => { command.arg("--cached").env("GIT_INDEX_FILE", file); },
    }
    command.args(["-z", "--stdin"]).args(attributes);
    let response = run_bounded(command, Some(&request), GIT_OUTPUT_LIMIT)?;
    Ok(AttrAnswer { request, response })
}

/// What `check_attr` sent Git (`nul_terminated` paths) and Git's answer.
struct AttrAnswer {
    request: Vec<u8>,
    response: Vec<u8>,
}

/// Each path joined into one buffer, each followed by NUL.
pub(crate) fn nul_terminated<P: AsRef<[u8]>>(paths: &[P]) -> Vec<u8> {
    paths.iter().flat_map(|path| path.as_ref().iter().copied().chain([0])).collect()
}

/// For each path, whether Git's effective `filter` attribute is
/// `transcrypt-v3`. Git evaluates its own attribute rules (patterns, nested
/// files, macros, `.git/info/attributes`); the whole answer is parsed by the
/// verified core (`parse_attr_response_spec`), which requires one record per
/// requested path, in order, and nothing else.
pub(crate) fn protected_flags(root: &Path, paths: &[&[u8]], from: Attributes) -> Result<Vec<bool>, String> {
    if paths.is_empty() { return Ok(Vec::new()); }
    let answer = check_attr(root, paths, from, &["filter"])?;
    let mut flags = vec![false; paths.len()];
    if !parse_attr_response(&answer.request, &answer.response, &mut flags) {
        return Err("unexpected git check-attr output".into());
    }
    Ok(flags)
}

/// For each entry of `listing`, whether Git's effective `filter` attribute
/// is `transcrypt-v3`. Git's answer is parsed by the verified core against
/// the listing's own paths (`parse_listing_attrs_spec`): one record per
/// entry, in order, naming exactly that entry's path, and nothing else.
pub(crate) fn listing_flags(root: &Path, listing: &Listing, from: Attributes) -> Result<Vec<bool>, String> {
    if listing.entries().is_empty() { return Ok(Vec::new()); }
    let answer = check_attr(root, &paths_of(listing.entries()), from, &["filter"])?;
    listing.attribute_flags(&answer.response).ok_or_else(|| "unexpected git check-attr output".into())
}

/// For each path, its value of each of `attributes` (`unspecified`, `unset`,
/// `set` or a value), for checks that only ever refuse: an answer that does
/// not name exactly the requested paths and attributes, in order, is an error.
pub(crate) fn attr_values(root: &Path, paths: &[&[u8]], from: Attributes, attributes: &[&str])
    -> Result<Vec<Vec<Vec<u8>>>, String>
{
    if paths.is_empty() { return Ok(Vec::new()); }
    let response = check_attr(root, paths, from, attributes)?.response;
    let fields: Vec<&[u8]> = response.split(|b| *b == 0).collect();
    let width = CHECK_ATTR_FIELDS * attributes.len();
    if fields.len() != width * paths.len() + 1 || fields.last() != Some(&&b""[..]) {
        return Err("unexpected git check-attr output".into());
    }
    paths.iter().zip(fields.chunks(width)).map(|(path, record)| {
        record.chunks(CHECK_ATTR_FIELDS).zip(attributes).map(|(field, name)| match field {
            [p, n, value] if p == path && *n == name.as_bytes() => Ok(value.to_vec()),
            _ => Err("unexpected git check-attr output".into()),
        }).collect()
    }).collect()
}

/// Each path's `filter` attribute value.
pub(crate) fn filter_values(root: &Path, paths: &[&[u8]], from: Attributes) -> Result<Vec<Vec<u8>>, String> {
    Ok(attr_values(root, paths, from, &["filter"])?.into_iter().flatten().collect())
}

/// Whether a `filter` value hands the file to another named filter driver
/// (not unset or unspecified, which are deliberate exclusions).
pub(crate) fn other_filter(value: &[u8]) -> bool {
    value != FILTER_DRIVER && !matches!(value, b"unspecified" | b"unset")
}

/// Whether Git resolves the `transcrypt` macro to `filter=transcrypt-v3`
/// for a commit whose top-level `.gitattributes` is the blob `top`: probed
/// in a temporary index (in `index_dir`) holding that file and a directory
/// whose own rules say `probe transcrypt`. Local attribute files apply, as
/// they do to Git's filters. A missing, redefined or overridden macro all
/// show as a probe Git would not encrypt. The hooks and the audit use this
/// one predicate.
pub(crate) fn macro_resolves(root: &Path, index_dir: &Path, top: Option<&str>) -> Result<bool, String> {
    let rules = hash_object(root, b"probe transcrypt\n")?;
    let mut info = Vec::new();
    push_index_record(&mut info, REGULAR_FILE_MODE, &rules, b"transcrypt-v3-probe/.gitattributes");
    if let Some(top) = top { push_index_record(&mut info, REGULAR_FILE_MODE, top, &ATTRIBUTES_NAME); }
    let index = index_dir.join(format!("transcrypt-v3-probe-{}.index", std::process::id()));
    let _ = std::fs::remove_file(&index);
    let mut command = git_command(Some(root));
    command.env("GIT_INDEX_FILE", &index).args(["update-index", "-z", "--index-info"]);
    let result = run_bounded(command, Some(&info), SHORT_OUTPUT_LIMIT)
        .and_then(|_| protected_flags(root, &[b"transcrypt-v3-probe/probe"], Attributes::Index(&index)));
    let _ = std::fs::remove_file(&index);
    Ok(result?.first() == Some(&true))
}

/// A path marked `transcrypt` whose `filter` is neither `transcrypt-v3` nor
/// explicitly unset: the macro is broken for it, whatever any probe says
/// (a rule can target the probe's own path). `None` when there is none.
pub(crate) fn marked_unfiltered(root: &Path, paths: &[&[u8]], from: Attributes) -> Result<Option<String>, String> {
    let values = attr_values(root, paths, from, &["transcrypt", "filter"])?;
    for (path, values) in paths.iter().zip(&values) {
        let [mark, filter] = &values[..] else { return Err("unexpected git check-attr output".into()) };
        if mark == b"set" && *filter != FILTER_DRIVER && filter != b"unset" {
            let name = String::from_utf8_lossy(path);
            return Ok(Some(if filter == b"unspecified" {
                format!("{name}: {}", crate::attributes::MACRO_MISSING)
            } else {
                format!("{name} is marked `transcrypt`, but another rule gives it the filter `{}` (from \
                    `git lfs track`?), so it would be stored unencrypted; narrow that rule",
                    String::from_utf8_lossy(filter))
            }));
        }
    }
    Ok(None)
}

/// The entries among `entries` that Git's attributes protect.
pub(crate) fn protected_entries(root: &Path, entries: Vec<Staged>, from: Attributes) -> Result<Vec<Staged>, String> {
    let flags = protected_flags(root, &paths_of(&entries), from)?;
    Ok(entries.into_iter().zip(flags).filter(|(_, protected)| *protected).map(|(e, _)| e).collect())
}
