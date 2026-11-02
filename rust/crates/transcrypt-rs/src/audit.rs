//! Audit of committed history (keyed or keyless), and the pre-push hook
//! built on it.

use std::{
    cell::RefCell,
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
    git::{changed_files, Changes, PathBlob, CONFIG_PATH, config_blob, git, git_blob, git_command, is_attributes_path, paths_of, protected_flags,
        push_index_record, read_record, tree_files, Attributes, Mode, ObjectId, Repository, Staged, SHORT_OUTPUT_LIMIT},
};
use transcrypt_v3_core::{
    audit_check, is_object_id, is_reserved_path, reads_blob, staged_verdict, AuditBase, AuditedEntry, EntryCheck,
    StagedCheck, StagedEvidence, StagedRefusal, ATTRIBUTES_NAME, ID_LEN,
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
pub(crate) fn audit(repo: &Repository, revs: &[OsString], keyed: bool, max_commits: Option<usize>) -> Result<Audited, String> {
    let mut command = git_command(repo);
    command.args(["rev-list", "--reverse", "--parents"]);
    if revs.is_empty() { command.arg("HEAD"); } else { command.args(revs); }
    command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::null());
    let mut child = command.spawn().map_err(|e| format!("cannot run git rev-list: {e}"))?;
    let stdout = child.stdout.take().ok_or("git rev-list output pipe missing")?;
    let mut lines = io::BufReader::new(stdout);
    let mut state = AuditState::new(repo.git_dir());
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
            audit_commit(repo, keyed, &mut state, &text(ids[0]), ids.get(1).map(|p| text(p)))?;
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
    configs: HashMap<ObjectId, CommittedConfig>,
    /// The config blob of every commit audited so far (`None`: no config).
    commit_configs: HashMap<String, Option<ObjectId>>,
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
    oid: ObjectId,
    config_oid: ObjectId,
    path: Vec<u8>,
}

/// The `.gitattributes` blobs of a tree, in tree order.
type AttributeFiles = Vec<PathBlob>;

fn attribute_files(entries: &[Staged]) -> AttributeFiles {
    entries.iter().filter(|e| e.regular() && is_attributes_path(&e.path))
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
    fn protected(&mut self, repo: &Repository, files: &Rc<AttributeFiles>, paths: &[&[u8]]) -> Result<Vec<bool>, String> {
        if self.files.as_ref() != Some(files) {
            let _ = std::fs::remove_file(&self.file);
            self.files = None;
            if !files.is_empty() {
                let mut info = Vec::new();
                for file in files.iter() { push_index_record(&mut info, Mode::REGULAR, &file.oid, &file.path); }
                let mut command = git_command(repo);
                command.env("GIT_INDEX_FILE", &self.file).args(["update-index", "-z", "--index-info"]);
                let finished = crate::git::run_bounded_status(command, Some(&info), SHORT_OUTPUT_LIMIT)?;
                if !finished.status.success() {
                    return Err(format!("cannot read a commit's .gitattributes: {}", String::from_utf8_lossy(&finished.errors)));
                }
            }
            self.files = Some(files.clone());
        }
        protected_flags(repo, paths, Attributes::Index(&self.file))
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

/// Audit one commit against its first parent (`parent`). With the key of
/// the commit's configuration this establishes the hook's record invariant
/// of the commit (`RecordsAuthentic`: every regular, non-reserved entry whose
/// blob has the configuration's envelope authenticates at its own path),
/// given the parent's when the configuration is unchanged, and so every
/// selected entry authenticates (`keyed_audit_authenticates_commit`).
///
/// The entries examined are those the commit adds or changes (`diff-tree`
/// against the parent), or its whole tree when it is a root commit or changes
/// the config or an attribute file; every other entry is the parent's exactly
/// (A20). Each examined entry is checked by the verified `audit_check` and
/// `staged_verdict`, the pre-commit hook's vocabulary: a selected entry
/// authenticates (keyless: has the envelope and, unless the parent holds it,
/// is not a moved blob); an unprotected file the parent holds exactly is
/// trusted from the parent while the config is unchanged (`AuditBase::Parent`),
/// and any other unprotected file, with the key, authenticates if it is a
/// record (only its prefix is read to tell).
fn audit_commit(repo: &Repository, keyed: bool, state: &mut AuditState, commit: &str, parent: Option<String>)
    -> Result<(), String>
{
    let Changes { entries: changed, deleted, modified } = changed_files(repo, commit, parent.as_deref())?;
    let touched = |test: &dyn Fn(&[u8]) -> bool| changed.iter().any(|e| test(&e.path)) || deleted.iter().any(|d| test(&d.path));
    let config_changed = parent.is_none() || touched(&|p| p == CONFIG_PATH.as_bytes());
    let attributes_changed = parent.is_none() || touched(&is_attributes_path);
    // A new config re-binds every record, and new attributes may protect
    // files the commit did not change: examine the whole tree. An entry the
    // diff does not list is the parent's exactly (the parent holds it).
    let whole_tree = (config_changed || attributes_changed) && parent.is_some();
    let changed_paths: HashSet<Vec<u8>> = changed.iter().map(|e| e.path.clone()).collect();
    let mut entries = if whole_tree { tree_files(repo, commit)? } else { changed };
    // The commit's config blob and attribute files: from its tree when they
    // changed, else the parent's (looked up directly if the parent was not
    // audited).
    let parent_id = parent.unwrap_or_default();
    let config_oid = if config_changed {
        entries.iter().find(|e| e.path == CONFIG_PATH.as_bytes() && e.regular()).map(|e| e.oid.clone())
    } else {
        match state.commit_configs.get(&parent_id) {
            Some(known) => known.clone(),
            None => config_blob(repo, &parent_id)?,
        }
    };
    state.commit_configs.insert(commit.to_owned(), config_oid.clone());
    let attributes = if attributes_changed {
        Rc::new(attribute_files(&entries))
    } else {
        match state.commit_attributes.get(&parent_id) {
            Some(known) => known.clone(),
            None => Rc::new(attribute_files(&tree_files(repo, &parent_id)?)),
        }
    };
    state.commit_attributes.insert(commit.to_owned(), attributes.clone());
    // Repository metadata is never encrypted, whatever the attributes say.
    entries.retain(|e| !is_reserved_path(&e.path));
    let paths = paths_of(&entries);
    let flags = state.policy.protected(repo, &attributes, &paths)?;
    // The first deleted path of each removed blob, and the old blob of each
    // modified path.
    let mut moved: HashMap<&ObjectId, &[u8]> = HashMap::new();
    for d in &deleted { moved.entry(&d.oid).or_insert(d.path.as_slice()); }
    let old: HashMap<&[u8], &ObjectId> = modified.iter().map(|m| (m.path.as_slice(), &m.oid)).collect();
    let Some(config_oid) = config_oid else {
        // No configuration, so no records: only a protected file is wrong.
        return match entries.iter().zip(&flags).find(|(_, selected)| **selected) {
            Some((entry, _)) => Err(format!("{}: protected file in a commit without a v3 configuration (plaintext?)",
                at(commit, &entry.path))),
            None => Ok(()),
        };
    };
    check_policy(repo, &state.policy, commit, &attributes, &paths, config_changed || attributes_changed)?;
    if entries.is_empty() { return Ok(()); }
    let id = committed_config(repo, keyed, state, commit, &config_oid)?.id;
    // A file that was encrypted and is now handed to another named filter
    // (`git lfs track` writing `filter=lfs`) silently lost its protection.
    let was_record: Vec<(&Staged, &ObjectId)> = entries.iter().zip(&flags).filter(|(_, selected)| !**selected)
        .filter_map(|(e, _)| old.get(e.path.as_slice()).map(|oid| (e, *oid))).collect();
    check_drift(repo, &state.policy, commit, &id, was_record)?;
    let base = if config_changed { AuditBase::Tree } else { AuditBase::Parent };
    let examined = entries.iter().zip(&flags).map(|(entry, &selected)| (entry, AuditedEntry {
        regular: entry.regular(),
        selected,
        held: !changed_paths.contains(&entry.path),
        moved: moved.contains_key(&entry.oid),
    }));
    check_entries(repo, state, commit, &config_oid, base, examined, &moved)
}

/// The committed config `config_oid` (parsed and loaded once per run): its
/// id, and its key when the audit is keyed and this checkout is unlocked for
/// it. Whether a config has its key is therefore fixed for the whole run.
fn committed_config<'s>(repo: &Repository, keyed: bool, state: &'s mut AuditState, commit: &str, config_oid: &ObjectId)
    -> Result<&'s CommittedConfig, String>
{
    if !state.configs.contains_key(config_oid) {
        let bytes = git_blob(repo, config_oid)?;
        transcrypt_v3_core::parse_config(&bytes)
            .map_err(|_| format!("commit {commit}: invalid v3 configuration"))?;
        let id = transcrypt_rs::config_id(&bytes);
        let key = if keyed { Key::load(repo, &bytes)? } else { None };
        state.configs.insert(config_oid.clone(), CommittedConfig { id, key });
    }
    Ok(&state.configs[config_oid])
}

/// While a v3 config exists, the policy must define the `transcrypt` macro
/// (checked when either `changed`), and no file may be marked for v3
/// without its filter.
fn check_policy(repo: &Repository, policy: &AttributeIndex, commit: &str, attributes: &AttributeFiles, paths: &[&[u8]], changed: bool)
    -> Result<(), String>
{
    if changed {
        let top = attributes.iter().find(|a| a.path == ATTRIBUTES_NAME).map(|a| &a.oid);
        if !crate::git::macro_resolves(repo, top)? {
            return Err(format!("commit {commit}: {}", crate::attributes::MACRO_MISSING));
        }
    }
    // The policy index holds this commit's attributes (loaded by the caller).
    if let Some(problem) = crate::git::marked_unfiltered(repo, paths, Attributes::Index(&policy.file))? {
        return Err(format!("commit {commit}: {problem}"));
    }
    Ok(())
}

/// Unprotected files whose path held a record of the config `id` and that
/// another filter now takes. It only refuses, like the hook's `check_drift`.
fn check_drift(repo: &Repository, policy: &AttributeIndex, commit: &str, id: &[u8; ID_LEN],
    was_record: Vec<(&Staged, &ObjectId)>) -> Result<(), String>
{
    let is_record = |oid: &ObjectId| crate::git::is_record(repo, oid, id);
    let mut drifted = Vec::new();
    for (entry, old) in was_record {
        if is_record(old)? && !is_record(&entry.oid)? { drifted.push(entry.path.as_slice()); }
    }
    let values = crate::git::filter_values(repo, &drifted, Attributes::Index(&policy.file))?;
    if let Some((path, value)) = drifted.iter().zip(values).find(|(_, v)| crate::git::other_filter(v)) {
        return Err(format!("{}: was encrypted, and is now stored unencrypted for the filter `{}`; a \
            .gitattributes rule (e.g. from `git lfs track`) overrides `transcrypt`", at(commit, path),
            String::from_utf8_lossy(&value)));
    }
    Ok(())
}

/// Whether the cache settles `check` for an entry whose blob, config and
/// path it holds. The cache (`AuditState::checked`) gains an entry only after
/// a selected entry's check passed (`StagedCheck::Protected`), under a config
/// whose key is fixed for the run: so the blob has that config's envelope
/// and, when the config is keyed, opened at that path. That settles
/// `Authenticate` (asked only when keyed) and `Envelope`, which ask nothing
/// else; `EnvelopeNotMoved` also asks about this commit's deletions, and the
/// checks of unprotected files are never cached.
fn settled_by_cache(check: StagedCheck) -> bool {
    match check {
        StagedCheck::Protected(EntryCheck::Authenticate) => true,
        StagedCheck::Protected(EntryCheck::Envelope) => true,
        StagedCheck::Protected(EntryCheck::EnvelopeNotMoved) => false,
        StagedCheck::Skip => false,
        StagedCheck::NotRecord => false,
        StagedCheck::AuthenticateIfRecord => false,
    }
}

/// Check every examined entry of the commit under its config `config_oid`
/// (`audit_check`, then `staged_verdict`), each fact about the entry itself;
/// `moved` names, for messages, the deleted path a moved blob came from.
fn check_entries<'e>(repo: &Repository, state: &mut AuditState, commit: &str, config_oid: &ObjectId, base: AuditBase,
    examined: impl Iterator<Item = (&'e Staged, AuditedEntry)>, moved: &HashMap<&ObjectId, &[u8]>) -> Result<(), String>
{
    let CommittedConfig { id, key } = &state.configs[config_oid];
    for (entry, facts) in examined {
        let Some(check) = audit_check(facts, &entry.path, key.is_some(), base) else {
            return Err(format!("{}: protected path is not a regular file", at(commit, &entry.path)));
        };
        let checked = CheckedRecord { oid: entry.oid.clone(), config_oid: config_oid.clone(), path: entry.path.clone() };
        if settled_by_cache(check) && state.checked.contains(&checked) { continue; }
        let record = if reads_blob(check) {
            Some(git_blob(repo, &entry.oid).map_err(|e| format!("{}: {e}", at(commit, &entry.path)))?)
        } else {
            None
        };
        let evidence = AuditEvidence {
            repo, key: key.as_ref(), id, entry, moved: facts.moved, record: record.as_deref(),
            unopened: RefCell::new(None), failure: RefCell::new(None),
        };
        let verdict = staged_verdict(&evidence, check, record.as_deref().unwrap_or_default(), id);
        // An answer that could not be found refuses, whatever the verdict.
        if let Some(failure) = evidence.failure.take() {
            return Err(format!("{}: {failure}", at(commit, &entry.path)));
        }
        if let Err(refusal) = verdict {
            return Err(audit_refusal(refusal, commit, &evidence, moved.get(&entry.oid).copied()));
        }
        // Recorded only now that the check passed (see `settled_by_cache`).
        if let StagedCheck::Protected(_) = check {
            state.checked.insert(checked);
            state.records += 1;
        }
    }
    state.authenticated &= key.is_some();
    Ok(())
}

/// The audit's answers about one examined entry for the verified
/// `staged_verdict`, each about the entry's own blob (by object id) and path,
/// computed only when asked.
struct AuditEvidence<'a> {
    repo: &'a Repository,
    key: Option<&'a Key>,
    id: &'a [u8; ID_LEN],
    entry: &'a Staged,
    /// Whether the blob is that of a path the commit deletes.
    moved: bool,
    /// The blob, when the check read it (`reads_blob`).
    record: Option<&'a [u8]>,
    /// Why the blob did not open, for the message.
    unopened: RefCell<Option<String>>,
    /// Why an answer could not be found (a failed read): the check refuses.
    failure: RefCell<Option<String>>,
}

impl StagedEvidence for AuditEvidence<'_> {
    /// Its size and first bytes, decided by `record_envelope_prefix_ok`.
    fn is_record(&self) -> bool {
        crate::git::is_record(self.repo, &self.entry.oid, self.id).unwrap_or_else(|e| {
            self.failure.replace(Some(e));
            false
        })
    }

    /// `Key::open` at the entry's path.
    fn opens(&self) -> bool {
        let Some(key) = self.key else { return false };
        let read;
        let record = match self.record {
            Some(record) => record,
            None => match git_blob(self.repo, &self.entry.oid) {
                Ok(blob) => { read = blob; &read },
                Err(e) => {
                    self.failure.replace(Some(e));
                    return false;
                },
            },
        };
        match key.open(&self.entry.path, record) {
            Ok(_) => true,
            Err(e) => {
                self.unopened.replace(Some(e));
                false
            },
        }
    }

    /// Moved: the blob of a path this commit deletes.
    fn elsewhere(&self) -> bool {
        self.moved
    }
}

/// The message for the verified refusal of `evidence`'s entry in `commit`;
/// `from`: the deleted path its blob came from, if any.
fn audit_refusal(refusal: StagedRefusal, commit: &str, evidence: &AuditEvidence, from: Option<&[u8]>) -> String {
    let here = at(commit, &evidence.entry.path);
    let from = from.map(String::from_utf8_lossy).unwrap_or_default();
    let unopened = || evidence.unopened.take().unwrap_or_default();
    match refusal {
        StagedRefusal::Plaintext | StagedRefusal::OtherConfig | StagedRefusal::Envelope =>
            format!("{here}: not v3 ciphertext for its configuration (plaintext?)"),
        StagedRefusal::Moved => moved_here(&here, &from),
        StagedRefusal::Authentication if evidence.moved => moved_here(&here, &from),
        StagedRefusal::Authentication => format!("{here}: {}", unopened()),
        StagedRefusal::UnprotectedRecord => moved_away(&here, &from),
        StagedRefusal::UnprotectedForgery if evidence.moved => moved_away(&here, &from),
        StagedRefusal::UnprotectedForgery => format!("{here}: not protected, but holds a record of its \
            configuration that does not open there ({}): a forgery, or a record copied from another path, \
            which an attribute change would protect unauthenticated", unopened()),
    }
}

fn moved_here(here: &str, from: &str) -> String {
    format!("{here}: the encrypted {from} moved here without re-encryption (renamed while locked or with \
        --no-verify?); it cannot be decrypted at its new path")
}

fn moved_away(here: &str, from: &str) -> String {
    format!("{here}: the encrypted {from} moved to this unprotected name without decryption; nothing decrypts it here")
}

/// The pre-push hook: audit every commit being pushed that the remote does
/// not already have. Git supplies `<local ref> SP <local oid> SP <remote
/// ref> SP <remote oid>` lines on stdin.
pub(crate) fn pre_push(repo: &Repository, remote: Option<&OsStr>) -> Result<(), String> {
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
        if !zero(remote_oid) && git(repo, &["cat-file", "-e", &String::from_utf8_lossy(&known)]).is_ok() {
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
    audit(repo, &revs, true, None).map(|_| ())
        .map_err(|e| format!("{e}\nrefusing to push; see `transcrypt-rs audit`"))
}
