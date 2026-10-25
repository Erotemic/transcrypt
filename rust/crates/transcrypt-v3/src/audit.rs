//! Keyless audit of committed history, and the pre-push hook built on it.

use std::{
    collections::{HashMap, HashSet},
    ffi::{OsStr, OsString},
    io::{self, Read},
    path::{Path, PathBuf},
    process::Stdio,
    rc::Rc,
};
use std::os::unix::ffi::OsStringExt;
use crate::{
    credential::Key,
    git::{changed_files, config_blob, git, git_blob, git_command, protected_flags,
        read_limited, tree_files, Attributes, Staged},
};
use transcrypt_v3_core::{
    is_object_id, is_reserved_path, record_envelope_ok, ID_LEN, MAX_RECORD,
};

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
    let mut state = AuditState {
        authenticated: true,
        commits: 0,
        records: 0,
        configs: HashMap::new(),
        commit_configs: HashMap::new(),
        commit_attributes: HashMap::new(),
        policy: AttributeIndex { file: git_dir.join(format!("transcrypt-v3-audit-{}.index", std::process::id())), files: None },
        checked: HashSet::new(),
    };
    let result = (|| -> Result<(), String> {
        let mut line = Vec::new();
        loop {
            line.clear();
            use io::BufRead;
            (&mut lines).take(4096).read_until(b'\n', &mut line).map_err(|_| "cannot read git rev-list")?;
            if line.is_empty() { return Ok(()); }
            let ids: Vec<&[u8]> = line.strip_suffix(b"\n").ok_or("malformed git rev-list output")?
                .split(|b| *b == b' ').collect();
            if !ids.iter().all(|id| is_object_id(id)) {
                return Err("malformed git rev-list output".into());
            }
            state.commits += 1;
            if max_commits.is_some_and(|max| state.commits > max) {
                return Err(format!("more than {} commits to audit; refusing (raise --max-commits)",
                    max_commits.unwrap_or(0)));
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
    /// Per committed config blob: its bytes, id and the key, if this
    /// checkout is unlocked for it.
    configs: HashMap<String, Committed>,
    /// The config blob of every commit audited so far (`None`: no config).
    commit_configs: HashMap<String, Option<String>>,
    /// The `.gitattributes` files of every commit audited so far.
    commit_attributes: HashMap<String, Rc<AttributeFiles>>,
    policy: AttributeIndex,
    checked: HashSet<(String, String, Vec<u8>)>,
}

/// A committed config: its bytes, id and the key, if unlocked for it.
type Committed = (Vec<u8>, [u8; ID_LEN], Option<Key>);

/// The `.gitattributes` blobs of a tree: (path, object id), in tree order.
type AttributeFiles = Vec<(Vec<u8>, String)>;

fn attribute_file(path: &[u8]) -> bool {
    path == b".gitattributes" || path.ends_with(b"/.gitattributes")
}

fn attribute_files(entries: &[Staged]) -> AttributeFiles {
    entries.iter().filter(|e| e.regular && attribute_file(&e.path)).map(|e| (e.path.clone(), e.oid.clone())).collect()
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
                for (path, oid) in files.iter() {
                    info.extend_from_slice(format!("100644 {oid}\t").as_bytes());
                    info.extend_from_slice(path);
                    info.push(0);
                }
                let mut command = git_command(Some(root));
                command.env("GIT_INDEX_FILE", &self.file).args(["update-index", "-z", "--index-info"]);
                let (status, _, errors) = crate::git::run_bounded_status(command, Some(info), 1 << 20)?;
                if !status.success() {
                    return Err(format!("cannot read a commit's .gitattributes: {}", String::from_utf8_lossy(&errors)));
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

fn audit_commit(root: &Path, keyed: bool, state: &mut AuditState, commit: &str, parent: Option<String>)
    -> Result<(), String>
{
    let at = |path: &[u8]| format!("commit {commit}, {}", String::from_utf8_lossy(path));
    let (mut entries, deleted, modified) = match parent {
        Some(ref parent) => changed_files(root, commit, Some(parent))?,
        None => (tree_files(root, commit)?, Vec::new(), Vec::new()),
    };
    let touched = |test: &dyn Fn(&[u8]) -> bool| entries.iter().any(|e| test(&e.path)) || deleted.iter().any(|(p, _)| test(p));
    let config_changed = parent.is_none() || touched(&|p| p == b".transcrypt/config");
    let attributes_changed = parent.is_none() || touched(&attribute_file);
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
        entries.iter().find(|e| e.path == b".transcrypt/config" && e.regular).map(|e| e.oid.clone())
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
    let paths: Vec<&[u8]> = entries.iter().map(|e| e.path.as_slice()).collect();
    let flags = state.policy.protected(root, &attributes, &paths)?;
    let protected: Vec<&Staged> = entries.iter().zip(&flags).filter(|(_, p)| **p).map(|(e, _)| e).collect();
    let unprotected = entries.iter().zip(&flags).filter(|(_, p)| !**p).map(|(e, _)| e);
    // A record this commit moved from a deleted path to an unprotected one is
    // never decrypted there (`git mv x.env x.bak`, committed by any route).
    let unprotected: Vec<&Staged> = unprotected.collect();
    let moved_away: Vec<(&Staged, &[u8])> = unprotected.iter()
        .filter_map(|e| deleted.iter().find(|(_, oid)| *oid == e.oid).map(|(p, _)| (*e, p.as_slice())))
        .collect();
    // A file that was encrypted and is now handed to another named filter
    // (`git lfs track` writing `filter=lfs`) silently lost its protection.
    let was_record: Vec<&Staged> = unprotected.iter().copied()
        .filter(|e| modified.iter().any(|(p, _)| *p == e.path)).collect();
    // While a v3 config exists, the policy must define the `transcrypt`
    // macro (checked when either changes).
    if config_oid.is_some() && (config_changed || attributes_changed) {
        let top = attributes.iter().find(|(p, _)| p == b".gitattributes").map(|(_, oid)| oid.as_str());
        let dir = state.policy.file.parent().map(Path::to_path_buf).unwrap_or_default();
        if !crate::git::macro_resolves(root, &dir, top)? {
            return Err(format!("commit {commit}: {}", crate::setup::MACRO_MISSING));
        }
    }
    if config_oid.is_some() {
        let paths: Vec<&[u8]> = entries.iter().map(|e| e.path.as_slice()).collect();
        // The policy index holds this commit's attributes (loaded above).
        if let Some(problem) = crate::git::marked_unfiltered(root, &paths, Attributes::Index(&state.policy.file))? {
            return Err(format!("commit {commit}: {problem}"));
        }
    }
    if protected.is_empty() && moved_away.is_empty() && was_record.is_empty() { return Ok(()); }
    if let Some(config_oid) = &config_oid {
        let id = transcrypt_v3::config_id(&git_blob(root, config_oid)?);
        let is_record = |oid: &str| -> Result<bool, String> {
            Ok(crate::git::git_blob_if_record_sized(root, oid)?.is_some_and(|b| record_envelope_ok(&b, &id)))
        };
        for (entry, from) in moved_away {
            if is_record(&entry.oid)? {
                return Err(format!("{}: the encrypted {} moved to this unprotected name without decryption; \
                    nothing decrypts it here", at(&entry.path), String::from_utf8_lossy(from)));
            }
        }
        let mut drifted = Vec::new();
        for entry in was_record {
            let old = modified.iter().find(|(p, _)| *p == entry.path).map(|(_, oid)| oid.as_str()).unwrap_or_default();
            if is_record(old)? && !is_record(&entry.oid)? { drifted.push(entry.path.as_slice()); }
        }
        let values = crate::git::filter_values(root, &drifted, Attributes::Index(&state.policy.file))?;
        if let Some((path, value)) = drifted.iter().zip(values).find(|(_, v)| crate::git::other_filter(v)) {
            return Err(format!("{}: was encrypted, and is now stored unencrypted for the filter `{}`; a \
                .gitattributes rule (e.g. from `git lfs track`) overrides `transcrypt`", at(path),
                String::from_utf8_lossy(&value)));
        }
    }
    if protected.is_empty() { return Ok(()); }
    let Some(config_oid) = config_oid else {
        return Err(format!("{}: protected file in a commit without a v3 configuration (plaintext?)",
            at(&protected[0].path)));
    };
    if !state.configs.contains_key(&config_oid) {
        let bytes = git_blob(root, &config_oid)?;
        transcrypt_v3_core::parse_config(&bytes)
            .map_err(|_| format!("commit {commit}: invalid v3 configuration"))?;
        let id = transcrypt_v3::config_id(&bytes);
        let key = if keyed { Key::load(root, &bytes)? } else { None };
        state.configs.insert(config_oid.clone(), (bytes, id, key));
    }
    let (_, id, key) = &state.configs[&config_oid];
    // A blob this commit removed from one path and added at another is a
    // record moved without re-encryption: it does not open at its new path.
    let moved: HashMap<&str, &[u8]> = deleted.iter().map(|(p, oid)| (oid.as_str(), p.as_slice())).collect();
    for entry in protected {
        if !entry.regular {
            return Err(format!("{}: protected path is not a regular file", at(&entry.path)));
        }
        if !state.checked.insert((entry.oid.clone(), config_oid.clone(), entry.path.clone())) { continue; }
        let record = git_blob(root, &entry.oid).map_err(|e| format!("{}: {e}", at(&entry.path)))?;
        if !record_envelope_ok(&record, id) {
            return Err(format!("{}: not v3 ciphertext for its configuration (plaintext?)", at(&entry.path)));
        }
        if let Some(from) = moved.get(entry.oid.as_str()) {
            return Err(format!("{}: the encrypted {} moved here without re-encryption (renamed while \
                locked or with --no-verify?); it cannot be decrypted at its new path",
                at(&entry.path), String::from_utf8_lossy(from)));
        }
        if let Some(key) = key {
            key.open(&entry.path, &record).map_err(|e| format!("{}: {e}", at(&entry.path)))?;
        }
        state.records += 1;
    }
    if key.is_none() { state.authenticated = false; }
    Ok(())
}

/// The pre-push hook: audit every commit being pushed that the remote does
/// not already have. Git supplies `<local ref> SP <local oid> SP <remote
/// ref> SP <remote oid>` lines on stdin.
pub(crate) fn pre_push(root: &Path, remote: Option<&OsStr>) -> Result<(), String> {
    // Never silently drop refs: oversized input is refused, not truncated.
    let input = read_limited(io::stdin(), MAX_RECORD).map_err(|_| "cannot read pre-push input")?;
    let mut revs: Vec<OsString> = Vec::new();
    for line in input.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
        let fields: Vec<&[u8]> = line.split(|b| *b == b' ').collect();
        if fields.len() != 4 || !is_object_id(fields[1]) || !is_object_id(fields[3]) {
            return Err("malformed pre-push input".into());
        }
        let zero = |oid: &[u8]| oid.iter().all(|b| *b == b'0');
        if zero(fields[1]) { continue; } // deleting a remote ref pushes nothing
        revs.push(OsString::from_vec(fields[1].to_vec()));
        let mut known = fields[3].to_vec();
        known.extend_from_slice(b"^{commit}");
        if !zero(fields[3]) && git(root, &["cat-file", "-e", &String::from_utf8_lossy(&known)]).is_ok() {
            let mut exclude = b"^".to_vec();
            exclude.extend_from_slice(fields[3]);
            revs.push(OsString::from_vec(exclude));
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
        .map_err(|e| format!("{e}\nrefusing to push; see `transcrypt-v3 audit`"))
}
