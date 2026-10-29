//! Keyless audit of committed history, and the pre-push hook built on it.

use std::{
    collections::{HashMap, HashSet},
    ffi::{OsStr, OsString},
    io::{self, BufRead, Read},
    path::{Path, PathBuf},
    process::Stdio,
    rc::Rc,
};
use crate::{
    attributes::split_lines,
    credential::Key,
    git::{changed_files, Changes, PathBlob, CONFIG_PATH, config_blob, git, git_blob, git_command, is_attributes_file, paths_of, protected_flags,
        push_index_record, read_record, tree_files, Attributes, Staged, REGULAR_FILE_MODE, SHORT_OUTPUT_LIMIT},
};
use transcrypt_v3_core::{
    is_object_id, is_reserved_path, record_envelope_ok, ATTRIBUTES_NAME, ID_LEN,
};

/// The longest `git rev-list --parents` line read: a commit id and its
/// parents' ids, beyond which a line is malformed.
const REV_LIST_LINE_LIMIT: u64 = 4096;

/// A pre-push input line: `<local ref> <local oid> <remote ref> <remote oid>`.
const PRE_PUSH_FIELDS: usize = 4;
const PRE_PUSH_LOCAL_OID: usize = 1;
const PRE_PUSH_REMOTE_OID: usize = 3;

/// Result of `audit`.
pub(crate) struct Audited {
    pub(crate) records: usize,
    pub(crate) authenticated: bool,
}

/// Check committed history: in every commit `git rev-list <revs>` names
/// (default `HEAD`), every file that the commit's own `.gitattributes`
/// protect (as Git evaluates them) must be a regular file whose blob is a v3
/// record for the configuration committed in the same tree. This needs no
/// key, so it also runs in CI or a server-side hook; it cannot tell a
/// genuine record from a forged envelope. When this checkout is unlocked for
/// that configuration, each record is also authenticated at its path.
///
/// Each commit is checked for what it changes relative to its first parent
/// (its whole tree for a root commit or when it changes the config or any
/// `.gitattributes`). A parent outside the selected range is trusted: it is
/// already published (the pre-push and pre-receive ranges) or deliberately
/// excluded. Commits are streamed from `rev-list`, and `max_commits` bounds
/// the work a hostile push can demand of a server hook.
pub(crate) fn audit(root: &Path, revs: &[OsString], keyed: bool, max_commits: Option<usize>) -> Result<Audited, String> {
    let mut command = git_command(Some(root));
    command.args(["rev-list", "--reverse", "--parents"]);
    if revs.is_empty() { command.arg("HEAD"); } else { command.args(revs); }
    command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::null());
    let mut child = command.spawn().map_err(|e| format!("cannot run git rev-list: {e}"))?;
    let stdout = child.stdout.take().ok_or("git rev-list output pipe missing")?;
    let mut lines = io::BufReader::new(stdout);
    let git_dir = PathBuf::from(String::from_utf8(git(root, &["rev-parse", "--absolute-git-dir"])?)
        .map_err(|_| "Git directory path is not UTF-8")?.trim_end());
    let mut state = AuditState::new(&git_dir);
    let result = (|| -> Result<(), String> {
        let mut line = Vec::new();
        loop {
            line.clear();
            (&mut lines).take(REV_LIST_LINE_LIMIT).read_until(b'\n', &mut line).map_err(|_| "cannot read git rev-list")?;
            if line.is_empty() { return Ok(()); }
            let ids: Vec<&[u8]> = line.strip_suffix(b"\n").ok_or("malformed git rev-list output")?
                .split(|b| *b == b' ').collect();
            if !ids.iter().all(|id| is_object_id(id)) {
                return Err("malformed git rev-list output".into());
            }
            state.commits += 1;
            if let Some(max) = max_commits.filter(|max| state.commits > *max) {
                return Err(format!("more than {max} commits to audit; refusing (raise --max-commits)"));
            }
            let text = |id: &[u8]| String::from_utf8_lossy(id).into_owned();
            audit_commit(root, keyed, &mut state, &text(ids[0]), ids.get(1).map(|p| text(p)))?;
        }
    })();
    if result.is_err() { let _ = child.kill(); }
    let status = child.wait().map_err(|_| "cannot wait for git rev-list")?;
    result?;
    if !status.success() {
        return Err("git rev-list failed; check the revision arguments".into());
    }
    Ok(Audited { records: state.records, authenticated: state.authenticated })
}

struct AuditState {
    commits: usize,
    records: usize,
    authenticated: bool,
    /// Per committed config blob.
    configs: HashMap<String, CommittedConfig>,
    /// The config blob of every commit audited so far (`None`: no config).
    commit_configs: HashMap<String, Option<String>>,
    /// The `.gitattributes` files of every commit audited so far.
    commit_attributes: HashMap<String, Rc<AttributeFiles>>,
    policy: AttributeIndex,
    /// The records already checked (each blob once per config and path).
    checked: HashSet<CheckedRecord>,
}

impl AuditState {
    /// Nothing audited yet; the policy index is a temporary file in `git_dir`.
    fn new(git_dir: &Path) -> AuditState {
        AuditState {
            authenticated: true,
            commits: 0,
            records: 0,
            configs: HashMap::new(),
            commit_configs: HashMap::new(),
            commit_attributes: HashMap::new(),
            policy: AttributeIndex { file: git_dir.join(format!("transcrypt-v3-audit-{}.index", std::process::id())), files: None },
            checked: HashSet::new(),
        }
    }
}

/// A committed config: its id and the key, if this checkout is unlocked
/// for it.
struct CommittedConfig {
    id: [u8; ID_LEN],
    key: Option<Key>,
}

/// A record checked once: its blob, the config blob and the path.
#[derive(PartialEq, Eq, Hash)]
struct CheckedRecord {
    oid: String,
    config_oid: String,
    path: Vec<u8>,
}

/// The `.gitattributes` blobs of a tree, in tree order.
type AttributeFiles = Vec<PathBlob>;

fn attribute_files(entries: &[Staged]) -> AttributeFiles {
    entries.iter().filter(|e| e.regular && is_attributes_file(&e.path))
        .map(|e| PathBlob { path: e.path.clone(), oid: e.oid.clone() }).collect()
}

/// A temporary index holding exactly one commit's `.gitattributes` files,
/// so that `git check-attr --cached` answers with that commit's policy (on
/// every Git version, and in a bare repository).
struct AttributeIndex {
    file: PathBuf,
    files: Option<Rc<AttributeFiles>>,
}

impl AttributeIndex {
    fn protected(&mut self, root: &Path, files: &Rc<AttributeFiles>, paths: &[&[u8]]) -> Result<Vec<bool>, String> {
        if self.files.as_ref() != Some(files) {
            let _ = std::fs::remove_file(&self.file);
            self.files = None;
            if !files.is_empty() {
                let mut info = Vec::new();
                for file in files.iter() { push_index_record(&mut info, REGULAR_FILE_MODE, &file.oid, &file.path); }
                let mut command = git_command(Some(root));
                command.env("GIT_INDEX_FILE", &self.file).args(["update-index", "-z", "--index-info"]);
                let finished = crate::git::run_bounded_status(command, Some(&info), SHORT_OUTPUT_LIMIT)?;
                if !finished.status.success() {
                    return Err(format!("cannot read a commit's .gitattributes: {}", String::from_utf8_lossy(&finished.errors)));
                }
            }
            self.files = Some(files.clone());
        }
        protected_flags(root, paths, Attributes::Index(&self.file))
    }
}

impl Drop for AttributeIndex {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.file);
    }
}

/// `path` in `commit`, for messages.
fn at(commit: &str, path: &[u8]) -> String {
    format!("commit {commit}, {}", String::from_utf8_lossy(path))
}

fn audit_commit(root: &Path, keyed: bool, state: &mut AuditState, commit: &str, parent: Option<String>)
    -> Result<(), String>
{
    let Changes { mut entries, deleted, modified } = changed_files(root, commit, parent.as_deref())?;
    let touched = |test: &dyn Fn(&[u8]) -> bool| entries.iter().any(|e| test(&e.path)) || deleted.iter().any(|d| test(&d.path));
    let config_changed = parent.is_none() || touched(&|p| p == CONFIG_PATH.as_bytes());
    let attributes_changed = parent.is_none() || touched(&is_attributes_file);
    if (config_changed || attributes_changed) && parent.is_some() {
        // A new config re-binds every record, and new attributes may
        // protect files the commit did not change: check the whole tree.
        entries = tree_files(root, commit)?;
    }
    // The commit's config blob and attribute files: from its tree when they
    // changed, else the parent's (looked up directly if the parent was not
    // audited).
    let parent_id = parent.unwrap_or_default();
    let config_oid = if config_changed {
        entries.iter().find(|e| e.path == CONFIG_PATH.as_bytes() && e.regular).map(|e| e.oid.clone())
    } else {
        match state.commit_configs.get(&parent_id) {
            Some(known) => known.clone(),
            None => config_blob(root, &parent_id)?,
        }
    };
    state.commit_configs.insert(commit.to_owned(), config_oid.clone());
    let attributes = if attributes_changed {
        Rc::new(attribute_files(&entries))
    } else {
        match state.commit_attributes.get(&parent_id) {
            Some(known) => known.clone(),
            None => Rc::new(attribute_files(&tree_files(root, &parent_id)?)),
        }
    };
    state.commit_attributes.insert(commit.to_owned(), attributes.clone());
    // Repository metadata is never encrypted, whatever the attributes say.
    entries.retain(|e| !is_reserved_path(&e.path));
    let paths = paths_of(&entries);
    let flags = state.policy.protected(root, &attributes, &paths)?;
    let (mut protected, mut unprotected) = (Vec::new(), Vec::new());
    for (entry, &flag) in entries.iter().zip(&flags) {
        if flag { protected.push(entry) } else { unprotected.push(entry) }
    }
    // The first deleted path of each removed blob, and the old blob of each
    // modified path.
    let mut moved: HashMap<&str, &[u8]> = HashMap::new();
    for d in &deleted { moved.entry(d.oid.as_str()).or_insert(d.path.as_slice()); }
    let old: HashMap<&[u8], &str> = modified.iter().map(|m| (m.path.as_slice(), m.oid.as_str())).collect();
    // A record this commit moved from a deleted path to an unprotected one is
    // never decrypted there (`git mv x.env x.bak`, committed by any route).
    let moved_away: Vec<(&Staged, &[u8])> = unprotected.iter()
        .filter_map(|e| moved.get(e.oid.as_str()).map(|from| (*e, *from))).collect();
    // A file that was encrypted and is now handed to another named filter
    // (`git lfs track` writing `filter=lfs`) silently lost its protection.
    let was_record: Vec<(&Staged, &str)> = unprotected.iter()
        .filter_map(|e| old.get(e.path.as_slice()).map(|oid| (*e, *oid))).collect();
    if config_oid.is_some() {
        check_policy(root, &state.policy, commit, &attributes, &paths, config_changed || attributes_changed)?;
    }
    if protected.is_empty() && moved_away.is_empty() && was_record.is_empty() { return Ok(()); }
    if let Some(config_oid) = &config_oid {
        check_moves(root, &state.policy, commit, config_oid, moved_away, was_record)?;
    }
    if protected.is_empty() { return Ok(()); }
    let Some(config_oid) = config_oid else {
        return Err(format!("{}: protected file in a commit without a v3 configuration (plaintext?)",
            at(commit, &protected[0].path)));
    };
    check_records(root, keyed, state, commit, config_oid, protected, &moved)
}

/// While a v3 config exists, the policy must define the `transcrypt` macro
/// (checked when either `changed`), and no file may be marked for v3
/// without its filter.
fn check_policy(root: &Path, policy: &AttributeIndex, commit: &str, attributes: &AttributeFiles, paths: &[&[u8]], changed: bool)
    -> Result<(), String>
{
    if changed {
        let top = attributes.iter().find(|a| a.path == ATTRIBUTES_NAME).map(|a| a.oid.as_str());
        let dir = policy.file.parent().map(Path::to_path_buf).unwrap_or_default();
        if !crate::git::macro_resolves(root, &dir, top)? {
            return Err(format!("commit {commit}: {}", crate::attributes::MACRO_MISSING));
        }
    }
    // The policy index holds this commit's attributes (loaded by the caller).
    if let Some(problem) = crate::git::marked_unfiltered(root, paths, Attributes::Index(&policy.file))? {
        return Err(format!("commit {commit}: {problem}"));
    }
    Ok(())
}

/// Records of the config `config_oid` that this commit moved to an
/// unprotected path, or whose path another filter now takes.
fn check_moves(root: &Path, policy: &AttributeIndex, commit: &str, config_oid: &str, moved_away: Vec<(&Staged, &[u8])>,
    was_record: Vec<(&Staged, &str)>) -> Result<(), String>
{
    let id = transcrypt_rs::config_id(&git_blob(root, config_oid)?);
    let is_record = |oid: &str| crate::git::is_record(root, oid, &id);
    for (entry, from) in moved_away {
        if is_record(&entry.oid)? {
            return Err(format!("{}: the encrypted {} moved to this unprotected name without decryption; \
                nothing decrypts it here", at(commit, &entry.path), String::from_utf8_lossy(from)));
        }
    }
    let mut drifted = Vec::new();
    for (entry, old) in was_record {
        if is_record(old)? && !is_record(&entry.oid)? { drifted.push(entry.path.as_slice()); }
    }
    let values = crate::git::filter_values(root, &drifted, Attributes::Index(&policy.file))?;
    if let Some((path, value)) = drifted.iter().zip(values).find(|(_, v)| crate::git::other_filter(v)) {
        return Err(format!("{}: was encrypted, and is now stored unencrypted for the filter `{}`; a \
            .gitattributes rule (e.g. from `git lfs track`) overrides `transcrypt`", at(commit, path),
            String::from_utf8_lossy(&value)));
    }
    Ok(())
}

/// Every protected file of the commit is a regular file holding a record of
/// its config `config_oid`, at the path it was sealed for (authenticated
/// there when this checkout has the key).
fn check_records(root: &Path, keyed: bool, state: &mut AuditState, commit: &str, config_oid: String, protected: Vec<&Staged>,
    moved: &HashMap<&str, &[u8]>) -> Result<(), String>
{
    if !state.configs.contains_key(&config_oid) {
        let bytes = git_blob(root, &config_oid)?;
        transcrypt_v3_core::parse_config(&bytes)
            .map_err(|_| format!("commit {commit}: invalid v3 configuration"))?;
        let id = transcrypt_rs::config_id(&bytes);
        let key = if keyed { Key::load(root, &bytes)? } else { None };
        state.configs.insert(config_oid.clone(), CommittedConfig { id, key });
    }
    let CommittedConfig { id, key } = &state.configs[&config_oid];
    // A blob this commit removed from one path and added at another is a
    // record moved without re-encryption: it does not open at its new path.
    for entry in protected {
        if !entry.regular {
            return Err(format!("{}: protected path is not a regular file", at(commit, &entry.path)));
        }
        let checked = CheckedRecord { oid: entry.oid.clone(), config_oid: config_oid.clone(), path: entry.path.clone() };
        if !state.checked.insert(checked) { continue; }
        let record = git_blob(root, &entry.oid).map_err(|e| format!("{}: {e}", at(commit, &entry.path)))?;
        if !record_envelope_ok(&record, id) {
            return Err(format!("{}: not v3 ciphertext for its configuration (plaintext?)", at(commit, &entry.path)));
        }
        if let Some(from) = moved.get(entry.oid.as_str()) {
            return Err(format!("{}: the encrypted {} moved here without re-encryption (renamed while \
                locked or with --no-verify?); it cannot be decrypted at its new path",
                at(commit, &entry.path), String::from_utf8_lossy(from)));
        }
        if let Some(key) = key {
            key.open(&entry.path, &record).map_err(|e| format!("{}: {e}", at(commit, &entry.path)))?;
        }
        state.records += 1;
    }
    state.authenticated &= key.is_some();
    Ok(())
}

/// The pre-push hook: audit every commit being pushed that the remote does
/// not already have. Git supplies `<local ref> SP <local oid> SP <remote
/// ref> SP <remote oid>` lines on stdin.
pub(crate) fn pre_push(root: &Path, remote: Option<&OsStr>) -> Result<(), String> {
    // Never silently drop refs: oversized input is refused, not truncated.
    let input = read_record(io::stdin()).map_err(|_| "cannot read pre-push input")?;
    let mut revs: Vec<OsString> = Vec::new();
    for line in split_lines(&input).filter(|l| !l.is_empty()) {
        let fields: Vec<&[u8]> = line.split(|b| *b == b' ').collect();
        if fields.len() != PRE_PUSH_FIELDS {
            return Err("malformed pre-push input".into());
        }
        let (local, remote_oid) = (fields[PRE_PUSH_LOCAL_OID], fields[PRE_PUSH_REMOTE_OID]);
        if !is_object_id(local) || !is_object_id(remote_oid) {
            return Err("malformed pre-push input".into());
        }
        let zero = |oid: &[u8]| oid.iter().all(|b| *b == b'0');
        if zero(local) { continue; } // deleting a remote ref pushes nothing
        revs.push(String::from_utf8_lossy(local).into_owned().into());
        let mut known = remote_oid.to_vec();
        known.extend_from_slice(b"^{commit}");
        if !zero(remote_oid) && git(root, &["cat-file", "-e", &String::from_utf8_lossy(&known)]).is_ok() {
            let mut exclude = b"^".to_vec();
            exclude.extend_from_slice(remote_oid);
            revs.push(String::from_utf8_lossy(&exclude).into_owned().into());
        }
    }
    if revs.is_empty() { return Ok(()); }
    // Commits on this remote's tracking branches were audited when pushed.
    // Only a plain remote name is used as a pattern; anything else (a URL)
    // audits the complete history being pushed.
    if let Some(name) = remote.and_then(OsStr::to_str) {
        if !name.is_empty() && name.bytes().all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b)) {
            revs.push("--not".into());
            revs.push(format!("--remotes={name}").into());
        }
    }
    audit(root, &revs, true, None).map(|_| ())
        .map_err(|e| format!("{e}\nrefusing to push; see `transcrypt-rs audit`"))
}
