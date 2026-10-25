//! Keyless audit of committed history, and the pre-push hook built on it.

use std::{
    collections::{HashMap, HashSet},
    ffi::{OsStr, OsString},
    io::{self, Read},
    path::Path,
    process::Stdio,
};
use std::os::unix::ffi::OsStringExt;
use crate::{
    git::{changed_files, config_blob, git, git_blob, git_command, read_limited, tree_files, Staged},
    protected_path,
    session::{self, Operation},
    setup::plaintext_copy_name,
};
use transcrypt_v3_core::{
    is_object_id, record_envelope_ok, MAX_RECORD,
};

/// Result of `audit`.
pub(crate) struct Audited {
    pub(crate) records: usize,
    pub(crate) authenticated: bool,
}

/// Check committed history: in every commit `git rev-list <revs>` names
/// (default `HEAD`), every `*.secret` entry must be a regular file whose blob
/// is a v3 record for the configuration committed in the same tree. This
/// needs no key, so it also runs in CI or a server-side hook. When the agent
/// is unlocked for that configuration, each record is also authenticated at
/// its path.
///
/// Each commit is checked for what it changes relative to its first parent
/// (its whole tree for a root commit or when it changes the config). A
/// parent outside the selected range is trusted: it is already published
/// (the pre-push and pre-receive ranges) or deliberately excluded. Commits
/// are streamed from `rev-list`, and `max_commits` bounds the work a hostile
/// push can demand of a server hook.
pub(crate) fn audit(root: &Path, revs: &[OsString], keyed: bool, max_commits: Option<usize>) -> Result<Audited, String> {
    let mut command = git_command(Some(root));
    command.args(["rev-list", "--reverse", "--parents"]);
    if revs.is_empty() { command.arg("HEAD"); } else { command.args(revs); }
    command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::null());
    let mut child = command.spawn().map_err(|e| format!("cannot run git rev-list: {e}"))?;
    let stdout = child.stdout.take().ok_or("git rev-list output pipe missing")?;
    let mut lines = io::BufReader::new(stdout);
    let mut state = AuditState { authenticated: true, ..AuditState::default() };
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

#[derive(Default)]
struct AuditState {
    commits: usize,
    records: usize,
    authenticated: bool,
    /// Per committed config blob: its bytes, id and whether the agent serves it.
    configs: HashMap<String, (Vec<u8>, [u8; transcrypt_v3_core::ID_LEN], bool)>,
    /// The config blob of every commit audited so far (`None`: no config).
    commit_configs: HashMap<String, Option<String>>,
    checked: HashSet<(String, String, Vec<u8>)>,
}

fn audit_commit(root: &Path, keyed: bool, state: &mut AuditState, commit: &str, parent: Option<String>)
    -> Result<(), String>
{
    let at = |path: &[u8]| format!("commit {commit}, {}", String::from_utf8_lossy(path));
    let mut entries = match parent {
        Some(ref parent) => changed_files(root, commit, Some(parent))?,
        None => tree_files(root, commit)?,
    };
    let config_changed = parent.is_none() || entries.iter().any(|e| e.path == b".transcrypt/config");
    if config_changed && parent.is_some() {
        // A new config re-binds every record in the tree: check them all.
        entries = tree_files(root, commit)?;
    }
    // The commit's config blob: from its tree when it changed, else the
    // parent's (looked up directly if the parent was not audited).
    let config_oid = if config_changed {
        entries.iter().find(|e| e.path == b".transcrypt/config" && e.regular).map(|e| e.oid.clone())
    } else {
        let parent = parent.unwrap_or_default();
        match state.commit_configs.get(&parent) {
            Some(known) => known.clone(),
            None => config_blob(root, &parent)?,
        }
    };
    state.commit_configs.insert(commit.to_owned(), config_oid.clone());
    if let Some(copy) = entries.iter().find(|e| plaintext_copy_name(&e.path)) {
        return Err(format!("{}: looks like an unencrypted editor or merge copy of a secret; \
            remove it from the commit", at(&copy.path)));
    }
    let protected: Vec<&Staged> = entries.iter().filter(|e| protected_path(&e.path)).collect();
    if protected.is_empty() { return Ok(()); }
    let Some(config_oid) = config_oid else {
        return Err(format!("{}: *.secret file in a commit without a v3 configuration (plaintext?)",
            at(&protected[0].path)));
    };
    if !state.configs.contains_key(&config_oid) {
        let bytes = git_blob(root, &config_oid)?;
        transcrypt_v3_core::parse_config(&bytes)
            .map_err(|_| format!("commit {commit}: invalid v3 configuration"))?;
        let id = transcrypt_v3::config_id(&bytes);
        let live = keyed && session::request(root, &bytes, Operation::Ping, &[], &[]).is_ok();
        state.configs.insert(config_oid.clone(), (bytes, id, live));
    }
    let (config, id, live) = state.configs[&config_oid].clone();
    for entry in protected {
        if !entry.regular {
            return Err(format!("{}: protected path is not a regular file", at(&entry.path)));
        }
        if !state.checked.insert((entry.oid.clone(), config_oid.clone(), entry.path.clone())) { continue; }
        let record = git_blob(root, &entry.oid).map_err(|e| format!("{}: {e}", at(&entry.path)))?;
        if !record_envelope_ok(&record, &id) {
            return Err(format!("{}: not v3 ciphertext for its configuration (plaintext?)", at(&entry.path)));
        }
        if live {
            session::request(root, &config, Operation::Decrypt, &entry.path, &record)
                .map_err(|e| format!("{}: {e}", at(&entry.path)))?;
        }
        state.records += 1;
    }
    if !live { state.authenticated = false; }
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
