//! Git's attribute answers (`check-attr`), parsed by the verified core.

use super::*;
use transcrypt_v3_core::admission_selected;

/// Which attribute files Git consults to decide what is protected.
#[derive(Clone, Copy)]
pub(crate) enum Attributes<'a> {
    /// The staged `.gitattributes` files: what the next commit will say.
    /// Protection is the committed policy's or a local source's
    /// (`admission_selected`).
    Staged,
    /// The worktree's, with every local source: what `git add` applies to
    /// a new file.
    Worktree,
    /// Those of a policy index (a commit's, for `audit`), as for `Staged`.
    Index(&'a Policy),
}

/// An isolated Git directory whose index holds only a policy's
/// `.gitattributes` files (a commit's, or the staged ones). `check-attr`
/// run there evaluates exactly those files, with Git's own matching, and no
/// local attribute source: the directory has no `info/attributes` and no
/// config, `HOME` and `XDG_CONFIG_HOME` point into it (so no global
/// attributes file), and the system attributes and config, `GIT_ATTR_SOURCE`
/// and `GIT_CONFIG_*` overrides are cleared. Objects are read from the
/// repository's object directory. Removed when dropped.
pub(crate) struct Policy {
    dir: PathBuf,
    objects: PathBuf,
    /// The `--index-info` of the files the index holds now.
    loaded: Option<Vec<u8>>,
}

impl Policy {
    pub(crate) fn new(repo: &Repository) -> Result<Policy, String> {
        let objects = git(repo, &["rev-parse", "--path-format=absolute", "--git-path", "objects"])?;
        let objects = objects.strip_suffix(b"\n").filter(|p| !p.is_empty()).ok_or("malformed git rev-parse output")?;
        let objects = PathBuf::from(crate::os::os_string(objects)?);
        // Unique per policy: several may be open at once (the audit's and
        // the macro probe's).
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = repo.git_dir().join(format!("transcrypt-v3-policy-{}-{n}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let created = std::fs::create_dir_all(dir.join("refs")).and_then(|_| std::fs::create_dir_all(dir.join("objects")))
            .and_then(|_| std::fs::write(dir.join("HEAD"), b"ref: refs/heads/policy\n"));
        let policy = Policy { dir, objects, loaded: None };
        created.map_err(|e| format!("cannot create {}: {e}", policy.dir.display()))?;
        Ok(policy)
    }

    /// The staged `.gitattributes` files (every stage of each).
    pub(crate) fn staged(repo: &Repository) -> Result<Policy, String> {
        let mut command = git_command(repo);
        command.env_remove("GIT_LITERAL_PATHSPECS").args(["ls-files", "-s", "-z", "--", ":(top,glob)**/.gitattributes"]);
        let info = run_bounded(command, None, GIT_OUTPUT_LIMIT)?;
        let mut policy = Policy::new(repo)?;
        policy.load(&info)?;
        Ok(policy)
    }

    /// Hold exactly the files of `files`.
    pub(crate) fn load_files(&mut self, files: &[PathBlob]) -> Result<(), String> {
        let mut info = Vec::new();
        for file in files { push_index_record(&mut info, Mode::REGULAR, &file.oid, &file.path); }
        self.load(&info)
    }

    /// Hold exactly the entries of `info` (`update-index --index-info`).
    fn load(&mut self, info: &[u8]) -> Result<(), String> {
        if self.loaded.as_deref() == Some(info) { return Ok(()); }
        self.loaded = None;
        let _ = std::fs::remove_file(self.index());
        if !info.is_empty() {
            let mut command = self.command();
            command.args(["update-index", "-z", "--index-info"]);
            let finished = run_bounded_status(command, Some(info), SHORT_OUTPUT_LIMIT)?;
            if !finished.status.success() {
                return Err(format!("cannot read the .gitattributes files: {}", String::from_utf8_lossy(&finished.errors)));
            }
        }
        self.loaded = Some(info.to_vec());
        Ok(())
    }

    fn index(&self) -> PathBuf {
        self.dir.join("index")
    }

    /// A Git command that sees only this policy (see `Policy`).
    fn command(&self) -> Command {
        let mut command = Command::new("git");
        command.current_dir(&self.dir);
        for name in ["GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM",
            "GIT_ATTR_SOURCE", "GIT_WORK_TREE", "GIT_COMMON_DIR", "GIT_NAMESPACE"] {
            command.env_remove(name);
        }
        command.env("GIT_DIR", &self.dir).env("GIT_OBJECT_DIRECTORY", &self.objects).env("GIT_INDEX_FILE", self.index())
            .env("HOME", &self.dir).env("XDG_CONFIG_HOME", &self.dir)
            .env("GIT_CONFIG_NOSYSTEM", "1").env("GIT_ATTR_NOSYSTEM", "1")
            .env("GIT_LITERAL_PATHSPECS", "1").env("GIT_NO_REPLACE_OBJECTS", "1");
        command
    }
}

impl Drop for Policy {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// `git check-attr -z --stdin <attributes>` for `paths`, sent as raw bytes
/// (any valid Unix name works), from the attribute files `from` selects.
/// Patterns match case-sensitively (`core.ignorecase=false`) so that every
/// clone, on every file system, selects the same files.
fn check_attr(repo: &Repository, paths: &[&[u8]], from: Source, attributes: &[&str]) -> Result<AttrAnswer, String> {
    if paths.iter().any(|path| path.is_empty() || path.contains(&0)) {
        return Err("invalid Git path".into());
    }
    let request = nul_terminated(paths);
    let mut command = match from {
        Source::Committed(policy) => policy.command(),
        _ => git_command(repo),
    };
    command.args(["-c", "core.ignorecase=false", "check-attr"]);
    match from {
        Source::Effective(Attributes::Staged) => { command.arg("--cached"); },
        Source::Effective(Attributes::Worktree) => {},
        Source::Effective(Attributes::Index(policy)) => { command.arg("--cached").env("GIT_INDEX_FILE", policy.index()); },
        Source::Committed(_) => { command.arg("--cached"); },
    }
    command.args(["-z", "--stdin"]).args(attributes);
    let response = run_bounded(command, Some(&request), GIT_OUTPUT_LIMIT)?;
    Ok(AttrAnswer { request, response })
}

/// Where `check_attr` asks: Git's effective attributes for `Attributes`
/// (every local source applied), or a policy's files alone.
#[derive(Clone, Copy)]
enum Source<'a> {
    Effective(Attributes<'a>),
    Committed(&'a Policy),
}

/// For `Staged` and `Index`, the verified `admission_selected` of the
/// committed policy's flag and Git's effective one, path by path: a local
/// attribute source (`.git/info/attributes`, `core.attributesFile`,
/// `GIT_ATTR_SOURCE`, ...) can add protection, never remove it. `Worktree`
/// answers Git's effective flags alone.
fn admitted(repo: &Repository, from: Attributes, flags: impl Fn(Source) -> Result<Vec<bool>, String>)
    -> Result<Vec<bool>, String>
{
    let effective = flags(Source::Effective(from))?;
    let committed = match from {
        Attributes::Worktree => return Ok(effective),
        Attributes::Staged => flags(Source::Committed(&Policy::staged(repo)?))?,
        Attributes::Index(policy) => flags(Source::Committed(policy))?,
    };
    if committed.len() != effective.len() { return Err("unexpected git check-attr output".into()); }
    Ok(committed.into_iter().zip(effective).map(|(c, e)| admission_selected(c, e)).collect())
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

/// For each path, whether `from` protects it (`filter=transcrypt-v3`; see
/// `admitted`). Git evaluates its own attribute rules (patterns, nested
/// files, macros); each answer is parsed by the verified core
/// (`parse_attr_response_spec`), which requires one record per requested
/// path, in order, and nothing else.
pub(crate) fn protected_flags(repo: &Repository, paths: &[&[u8]], from: Attributes) -> Result<Vec<bool>, String> {
    if paths.is_empty() { return Ok(Vec::new()); }
    admitted(repo, from, |source| source_flags(repo, paths, source))
}

fn source_flags(repo: &Repository, paths: &[&[u8]], from: Source) -> Result<Vec<bool>, String> {
    let answer = check_attr(repo, paths, from, &["filter"])?;
    let mut flags = vec![false; paths.len()];
    if !parse_attr_response(&answer.request, &answer.response, &mut flags) {
        return Err("unexpected git check-attr output".into());
    }
    Ok(flags)
}

/// For each entry of `listing`, whether `from` protects it (see
/// `admitted`). Each answer is parsed by the verified core against the
/// listing's own paths (`parse_listing_attrs_spec`): one record per entry,
/// in order, naming exactly that entry's path, and nothing else.
pub(crate) fn listing_flags(repo: &Repository, listing: &Listing, from: Attributes) -> Result<Vec<bool>, String> {
    if listing.entries().is_empty() { return Ok(Vec::new()); }
    let paths = paths_of(listing.entries());
    admitted(repo, from, |source| {
        let answer = check_attr(repo, &paths, source, &["filter"])?;
        listing.attribute_flags(&answer.response).ok_or_else(|| "unexpected git check-attr output".into())
    })
}

/// For each path, its value of each of `attributes` (`unspecified`, `unset`,
/// `set` or a value), for checks that only ever refuse: an answer that does
/// not name exactly the requested paths and attributes, in order, is an error.
pub(crate) fn attr_values(repo: &Repository, paths: &[&[u8]], from: Attributes, attributes: &[&str])
    -> Result<Vec<Vec<Vec<u8>>>, String>
{
    if paths.is_empty() { return Ok(Vec::new()); }
    let response = check_attr(repo, paths, Source::Effective(from), attributes)?.response;
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
pub(crate) fn filter_values(repo: &Repository, paths: &[&[u8]], from: Attributes) -> Result<Vec<Vec<u8>>, String> {
    Ok(attr_values(repo, paths, from, &["filter"])?.into_iter().flatten().collect())
}

/// Whether a `filter` value hands the file to another named filter driver
/// (not unset or unspecified, which are deliberate exclusions).
pub(crate) fn other_filter(value: &[u8]) -> bool {
    value != FILTER_DRIVER && !matches!(value, b"unspecified" | b"unset")
}

/// Whether Git resolves the `transcrypt` macro to `filter=transcrypt-v3`
/// for a commit whose top-level `.gitattributes` is the blob `top`: probed
/// in a policy index holding that file and a directory whose own rules say
/// `probe transcrypt`. It must resolve both from that file alone (what
/// every clone sees) and with every local attribute source applied (what
/// this checkout's Git filters do). A missing, redefined or overridden
/// macro all show as a probe Git would not encrypt. The hooks and the audit
/// use this one predicate.
pub(crate) fn macro_resolves(repo: &Repository, top: Option<&ObjectId>) -> Result<bool, String> {
    let rules = hash_object(repo, b"probe transcrypt\n")?;
    let mut info = Vec::new();
    push_index_record(&mut info, Mode::REGULAR, &rules, b"transcrypt-v3-probe/.gitattributes");
    if let Some(top) = top { push_index_record(&mut info, Mode::REGULAR, top, &ATTRIBUTES_NAME); }
    let mut policy = Policy::new(repo)?;
    policy.load(&info)?;
    let probe: &[&[u8]] = &[b"transcrypt-v3-probe/probe"];
    for source in [Source::Committed(&policy), Source::Effective(Attributes::Index(&policy))] {
        if source_flags(repo, probe, source)?.first() != Some(&true) { return Ok(false); }
    }
    Ok(true)
}

/// A path marked `transcrypt` whose `filter` is neither `transcrypt-v3` nor
/// explicitly unset: the macro is broken for it, whatever any probe says
/// (a rule can target the probe's own path). `None` when there is none.
pub(crate) fn marked_unfiltered(repo: &Repository, paths: &[&[u8]], from: Attributes) -> Result<Option<String>, String> {
    let values = attr_values(repo, paths, from, &["transcrypt", "filter"])?;
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
pub(crate) fn protected_entries(repo: &Repository, entries: Vec<Staged>, from: Attributes) -> Result<Vec<Staged>, String> {
    let flags = protected_flags(repo, &paths_of(&entries), from)?;
    Ok(entries.into_iter().zip(flags).filter(|(_, protected)| *protected).map(|(e, _)| e).collect())
}
