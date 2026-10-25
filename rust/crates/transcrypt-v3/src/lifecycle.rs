//! The index and worktree lifecycle: `verify-index` and the pre-commit
//! hook, `hydrate`, and `lock` (`flush` per worktree). Every decision to
//! publish, keep or replace bytes is made by the verified core.

use std::{collections::{HashMap, HashSet}, env, fs, path::{Path, PathBuf}};
use zeroize::Zeroizing;
use transcrypt_v3_core::{
    hydrate_action, is_reserved_path, lock_action, parse_file_header, record_envelope_ok, seal_action,
    HydrateAction, LockAction, SealAction,
};
use crate::{
    credential::Key,
    git::*,
    load_config,
    worktree::*,
};

/// The staged state that `check_index` verified: the exact index listing
/// and its protected entries.
pub(crate) struct Verified {
    pub(crate) listing: Vec<u8>,
    pub(crate) protected: Vec<Staged>,
}

/// The protected stage-0 entries of `entries`, by Git's staged attributes
/// (what the next commit will say), each a file Git filters and none of
/// them repository metadata.
pub(crate) fn staged_protected(root: &Path, entries: Vec<Staged>) -> Result<Vec<Staged>, String> {
    let protected = protected_entries(root, entries, Attributes::Staged)?;
    for entry in &protected {
        let name = String::from_utf8_lossy(&entry.path);
        if is_reserved_path(&entry.path) {
            return Err(format!("{name} is selected for encryption, but v3 never encrypts .gitattributes, \
                .gitmodules or .transcrypt/; narrow the .gitattributes pattern that selects it"));
        }
        if !entry.regular {
            return Err(format!("{name} is selected for encryption but is a symlink or submodule, \
                which Git stores unfiltered; narrow the pattern or replace it by a file"));
        }
    }
    Ok(protected)
}

/// Read one snapshot of the index and check it:
/// - the staged public config equals the worktree's;
/// - every protected entry is a file whose blob opens at its own path under
///   `key`; without a key, it has the envelope of this configuration and is
///   not the blob of another path in the index or `HEAD` (a record moved or
///   copied to another name would no longer open there, and only the key
///   can re-encrypt it);
/// - no unprotected entry staged since `HEAD` is a record of this
///   configuration: one moved to an unprotected name (`git mv x.env x.bak`)
///   would be committed where nothing ever decrypts it.
pub(crate) fn check_index(root: &Path, key: Option<&Key>) -> Result<Verified, String> {
    let config = load_config(root)?;
    let listing = git(root, &["ls-files", "--stage", "-z"])?;
    let entries = parse_listing(&listing)?;
    match entries.iter().find(|e| e.path == b".transcrypt/config") {
        Some(e) if e.regular && git_blob(root, &e.oid)? == config => {},
        _ => return Err("staged .transcrypt/config is missing, not a regular file or differs from the worktree \
            (an interrupted `rekey`? `git reset` undoes a staged rekey)".into()),
    }
    let top = entries.iter().find(|e| e.path == b".gitattributes" && e.regular).map(|e| e.oid.as_str());
    if !macro_resolves(root, &git_dir(root), top)? {
        return Err(crate::setup::MACRO_MISSING.into());
    }
    let head = head_files(root)?;
    let head_oid: HashMap<&[u8], &str> = head.iter().map(|e| (e.path.as_slice(), e.oid.as_str())).collect();
    let mut elsewhere: HashMap<String, Vec<u8>> = HashMap::new();
    for entry in head.iter().chain(entries.iter()) {
        elsewhere.entry(entry.oid.clone()).or_insert_with(|| entry.path.clone());
    }
    let changed: Vec<(Vec<u8>, String)> = entries.iter()
        .filter(|e| e.regular && head_oid.get(e.path.as_slice()) != Some(&e.oid.as_str()))
        .map(|e| (e.path.clone(), e.oid.clone())).collect();
    let protected = staged_protected(root, entries)?;
    let id = transcrypt_v3::config_id(&config);
    let is_record = |oid: &str| -> Result<bool, String> {
        Ok(git_blob_if_record_sized(root, oid)?.is_some_and(|blob| record_envelope_ok(&blob, &id)))
    };
    let mut drifted: Vec<&[u8]> = Vec::new();
    for (path, oid) in changed.iter().filter(|(p, _)| !protected.iter().any(|e| e.path == *p)) {
        if is_record(oid)? {
            return Err(format!("{} holds an encrypted record but is not protected (moved to an unprotected \
                name? or a pattern that matches it only case-insensitively: v3 matches case-sensitively, \
                so write it with the file's exact case): nothing would ever decrypt it there. Protect that \
                name, move the file back, or stage its plaintext", String::from_utf8_lossy(path)));
        }
        if head_oid.get(path.as_slice()).is_some_and(|old| is_record(old).unwrap_or(false)) {
            drifted.push(path);
        }
    }
    // A file encrypted in `HEAD` that another named filter now claims
    // (`git lfs track` writing `filter=lfs`) silently lost its protection;
    // `unprotect` and `-filter` exclusions are deliberate and allowed.
    let values = filter_values(root, &drifted, Attributes::Staged)?;
    for (path, value) in drifted.iter().zip(&values).filter(|(_, v)| !other_filter(v)) {
        eprintln!("transcrypt-v3: note: {} was encrypted in HEAD and is now staged unencrypted (`filter` is {}): \
            it is no longer selected by .gitattributes", String::from_utf8_lossy(path), String::from_utf8_lossy(value));
    }
    if let Some((path, value)) = drifted.iter().zip(values).find(|(_, v)| other_filter(v)) {
        return Err(format!("{} was encrypted and would now be stored unencrypted for the filter `{}`: a \
            .gitattributes rule (e.g. from `git lfs track`) overrides `transcrypt`. Narrow that rule, or \
            `transcrypt-v3 unprotect` the file deliberately", String::from_utf8_lossy(path),
            String::from_utf8_lossy(&value)));
    }
    for staged in &protected {
        let record = git_blob(root, &staged.oid)?;
        let name = String::from_utf8_lossy(&staged.path);
        if parse_file_header(&record).is_err() {
            return Err(format!("staged {name} is not encrypted (was it staged before it was protected?); \
                run `transcrypt-v3 protect` or `git add --renormalize -- {name}`"));
        }
        if parse_file_header(&record).is_ok_and(|found| found != id) {
            return Err(format!("staged {name} is encrypted under another config (cherry-picked or rebased \
                across a rekey?); run `transcrypt-v3 reencrypt` with that config's passphrase"));
        }
        match key {
            Some(key) => { key.open(&staged.path, &record).map_err(|e| format!("staged {name}: {e}; if it \
                was moved here, `git add --renormalize -- {name}` re-encrypts it from the worktree"))?; },
            None if !record_envelope_ok(&record, &id) =>
                return Err(format!("staged {name} is not v3 ciphertext for this repository")),
            None => if let Some(other) = elsewhere.get(&staged.oid).filter(|p| **p != staged.path) {
                return Err(format!("staged {name} holds the encrypted {}: a renamed or copied protected \
                    file must be committed while unlocked, which re-encrypts it for its new name",
                    String::from_utf8_lossy(other)));
            },
        }
    }
    Ok(Verified { listing, protected })
}

/// The files of `HEAD` (none before the first commit).
fn head_files(root: &Path) -> Result<Vec<Staged>, String> {
    if git(root, &["rev-parse", "-q", "--verify", "HEAD^{commit}"]).is_err() {
        return Ok(Vec::new());
    }
    tree_files(root, "HEAD")
}

/// Files as (path, object id) pairs.
type Files = HashSet<(Vec<u8>, String)>;

/// Every (path, blob) of the commits a merge, cherry-pick, revert or rebase
/// is bringing in: index content equal to one of them came from a commit and
/// is checked, never repaired. `None` when a rebase or `git am` is in
/// progress without a known commit: then nothing is repaired.
fn incoming(root: &Path) -> Result<Option<Files>, String> {
    let mut commits: Vec<String> = fs::read_to_string(git_dir(root).join("MERGE_HEAD")).unwrap_or_default()
        .lines().map(str::to_owned).collect();
    for name in ["CHERRY_PICK_HEAD", "REVERT_HEAD", "REBASE_HEAD"] {
        if let Ok(id) = git(root, &["rev-parse", "-q", "--verify", &format!("{name}^{{commit}}")]) {
            commits.push(String::from_utf8_lossy(&id).trim().to_owned());
        }
    }
    commits.retain(|c| transcrypt_v3_core::is_object_id(c.as_bytes()));
    if commits.is_empty() && ["rebase-merge", "rebase-apply"].iter().any(|dir| git_dir(root).join(dir).exists()) {
        return Ok(None);
    }
    let mut files = HashSet::new();
    for commit in commits {
        files.extend(tree_files(root, &commit)?.into_iter().map(|e| (e.path, e.oid)));
    }
    Ok(Some(files))
}

/// A commit without `.transcrypt/config` (a branch from before `init`):
/// the hooks accept exactly what the audit does, which is anything that
/// protects no file. Returns whether the index is such a commit.
fn configless(root: &Path) -> Result<bool, String> {
    let entries = indexed_files(root)?;
    if entries.iter().any(|e| e.path == b".transcrypt/config") { return Ok(false); }
    if let Some(entry) = staged_protected(root, entries)?.first() {
        return Err(format!("{} is protected, but this commit has no .transcrypt/config: it would be \
            stored unencrypted; check out .transcrypt/ from a branch that uses v3",
            String::from_utf8_lossy(&entry.path)));
    }
    Ok(true)
}

/// `verify-index`: the read-only check. Locked, it checks the keyless
/// envelopes, which still rejects any plaintext.
pub(crate) fn verify_index_command(root: &Path) -> Result<(), String> {
    if configless(root)? { return Ok(()); }
    let config = load_config(root)?;
    let key = Key::load(root, &config)?;
    check_index(root, key.as_ref())?;
    if key.is_none() {
        eprintln!("transcrypt-v3: locked; checked staged record envelopes only");
    }
    Ok(())
}

/// The pre-commit hook. First encrypt what ordinary Git commands stage
/// without the filter (`seal_staged`), then check the whole index.
pub(crate) fn pre_commit(root: &Path) -> Result<(), String> {
    if configless(root)? { return Ok(()); }
    let config = load_config(root)?;
    let key = Key::load(root, &config)?;
    if let Some(key) = &key {
        seal_staged(root, key, &[])?;
    }
    check_index(root, key.as_ref())?;
    if key.is_none() {
        eprintln!("transcrypt-v3: locked; checked staged record envelopes only");
    }
    if let Some(file) = crate::setup::filter_overrides(root).first() {
        eprintln!("transcrypt-v3: warning: {file} sets `filter`, which can unprotect files that \
            .gitattributes protects; see `transcrypt-v3 doctor`");
    }
    Ok(())
}

/// Encrypt the protected entries that the user staged without the clean
/// filter, and replace them in the index (same mode), so the commit holds
/// genuine records:
///
/// - **Plaintext** (no v3 envelope): a file tracked before a pattern
///   selected it, or `git mv` from an unprotected name. It is sealed at its
///   path; its earlier commits stay plaintext in history.
/// - **A renamed record**: `git mv` keeps the blob, which is bound to the
///   old path. If the same blob is in `HEAD` at a path whose index entry is
///   gone or replaced (a move, or a move and a new file in its place) and
///   opens there, its plaintext is sealed for the new path.
///
/// Only local changes are repaired (the verified `seal_action` decides): an
/// entry equal to `HEAD`'s, or equal to a file of a commit being merged,
/// picked, reverted or rebased, came from a commit, and re-encrypting it
/// would turn a hostile commit's moved or plaintext content into genuine
/// records; `check_index` refuses those instead. `force` lists paths whose
/// plaintext is sealed even when unchanged from `HEAD` (`protect` selecting
/// files committed before they were protected). Returns how many entries
/// were sealed.
pub(crate) fn seal_staged(root: &Path, key: &Key, force: &[Vec<u8>]) -> Result<usize, String> {
    let incoming = incoming(root)?;
    let listing = git(root, &["ls-files", "--stage", "-z"])?;
    let entries = parse_listing(&listing)?;
    let indexed: HashMap<Vec<u8>, String> = entries.iter().map(|e| (e.path.clone(), e.oid.clone())).collect();
    let protected = staged_protected(root, entries)?;
    let mut head_oid: HashMap<Vec<u8>, String> = HashMap::new();
    let mut moved_from: HashMap<String, Vec<Vec<u8>>> = HashMap::new();
    for entry in head_files(root)? {
        if indexed.get(&entry.path) != Some(&entry.oid) {
            moved_from.entry(entry.oid.clone()).or_default().push(entry.path.clone());
        }
        head_oid.insert(entry.path, entry.oid);
    }
    let mut index_info = Vec::new();
    let mut count = 0;
    for staged in &protected {
        let changed = head_oid.get(&staged.path) != Some(&staged.oid);
        let committed = incoming.as_ref().is_none_or(|files| files.contains(&(staged.path.clone(), staged.oid.clone())));
        let forced = force.contains(&staged.path);
        // `seal_action` never repairs a non-local entry; skip decrypting it
        // here (`check_index` verifies it right after).
        if !(changed && !committed) && !forced { continue; }
        let record = git_blob(root, &staged.oid).map_err(|e| format!("{}: {e}", String::from_utf8_lossy(&staged.path)))?;
        let opens = key.open(&staged.path, &record).is_ok();
        let envelope = parse_file_header(&record).is_ok();
        // `protect` may force sealing plaintext, never re-encrypting a record.
        let local = (changed && !committed) || (forced && !envelope);
        let moved = if opens || !envelope { None } else {
            moved_from.get(&staged.oid).map(Vec::as_slice).unwrap_or_default().iter()
                .filter(|p| **p != staged.path)
                .find_map(|p| key.open(p, &record).ok().map(|pt| (p, pt)))
        };
        let name = String::from_utf8_lossy(&staged.path).into_owned();
        // The verified core decides.
        let plaintext: Zeroizing<Vec<u8>> = match seal_action(opens, local, envelope, moved.is_some()) {
            SealAction::Keep | SealAction::Leave => continue,
            SealAction::Seal => {
                eprintln!("transcrypt-v3: encrypting {name}, which was staged unencrypted");
                Zeroizing::new(record)
            },
            SealAction::Rebind => {
                let Some((source, plaintext)) = moved else { continue };
                eprintln!("transcrypt-v3: re-encrypting {name} for its new name (it was {})",
                    String::from_utf8_lossy(source));
                plaintext
            },
        };
        let sealed = key.clean(&staged.path, &plaintext)?;
        let oid = hash_object(root, &sealed)?;
        index_info.extend_from_slice(format!("{} {oid}\t", staged.mode).as_bytes());
        index_info.extend_from_slice(&staged.path);
        index_info.push(0);
        count += 1;
    }
    if count > 0 {
        git_with_input(root, &["update-index", "-z", "--index-info"], &index_info)?;
    }
    Ok(count)
}

/// The plaintext of a staged protected record: opened at its own path, or,
/// for a record moved there by a local `git mv`, at the `HEAD` path it came
/// from (whose index entry is gone or replaced).
pub(crate) fn open_staged(root: &Path, key: &Key, staged: &Staged) -> Result<Zeroizing<Vec<u8>>, String> {
    let record = git_blob(root, &staged.oid)?;
    let error = match key.open(&staged.path, &record) {
        Ok(plaintext) => return Ok(plaintext),
        Err(e) => e,
    };
    let indexed: HashMap<Vec<u8>, String> = indexed_files(root)?.into_iter().map(|e| (e.path, e.oid)).collect();
    for entry in head_files(root)? {
        if entry.oid == staged.oid && entry.path != staged.path && indexed.get(&entry.path) != Some(&entry.oid) {
            if let Ok(plaintext) = key.open(&entry.path, &record) { return Ok(plaintext); }
        }
    }
    Err(format!("{}: {error}", String::from_utf8_lossy(&staged.path)))
}

/// Write `bytes` as a Git blob, unfiltered; its verified object id.
pub(crate) fn hash_object(root: &Path, bytes: &[u8]) -> Result<String, String> {
    let oid = git_with_input(root, &["hash-object", "-w", "--no-filters", "--stdin"], bytes)?;
    let oid = String::from_utf8(oid).map_err(|_| "malformed git hash-object output")?;
    let oid = oid.trim_end();
    if !transcrypt_v3_core::is_object_id(oid.as_bytes()) {
        return Err("malformed git hash-object output".into());
    }
    Ok(oid.to_owned())
}

/// Run from the post-checkout, post-merge and post-rewrite hooks. Only the
/// private mode needs it (its smudge filter leaves ciphertext when Git's
/// umask would expose plaintext); it never fails the finished Git command.
pub(crate) fn auto_hydrate(root: &Path) -> Result<(), String> {
    let Ok(config) = load_config(root) else { return Ok(()) };
    if !Key::load(root, &config).ok().flatten().is_some_and(|k| k.private()) {
        return Ok(());
    }
    match hydrate(root) {
        Ok(0) => {},
        Ok(n) => eprintln!("transcrypt-v3: decrypted {n} file(s) with mode 0600."),
        Err(e) => eprintln!("transcrypt-v3: automatic decryption skipped: {e}\n\
            Inspect with `transcrypt-v3 status`, then run `transcrypt-v3 hydrate`."),
    }
    Ok(())
}

/// Decrypt every protected worktree file that is an authentic record for
/// its own path: the staged ciphertext of a fresh checkout, or another
/// genuine record that Git wrote (a restored or stash-popped version). Every
/// other file (plaintext, edited or not) is left as it is (made private in
/// private mode). Nothing but an authentic record is ever replaced, so no
/// edit can be lost, and replacing a record by its plaintext loses nothing
/// (clean seals it back to the same record).
pub(crate) fn hydrate(root: &Path) -> Result<usize, String> {
    hydrate_locked(root, &staging_dir(root)?)
}

/// The protected paths among `paths`, by the staged attributes.
pub(crate) fn protected_paths(root: &Path, paths: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, String> {
    let refs: Vec<&[u8]> = paths.iter().map(Vec::as_slice).collect();
    let flags = protected_flags(root, &refs, Attributes::Staged)?;
    Ok(paths.iter().zip(flags).filter(|(_, p)| *p).map(|(p, _)| p.clone()).collect())
}

/// `hydrate` for a caller that already holds the staging lock.
pub(crate) fn hydrate_locked(root: &Path, staging: &Staging) -> Result<usize, String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let index = index_with_conflicts(root)?;
    let conflicted = protected_paths(root, &index.conflicted)?;
    let protected: Vec<Staged> = if conflicted.is_empty() {
        // Authenticate ALL staged protected objects and the staged config
        // before exposing any plaintext in the checkout.
        let verified = check_index(root, Some(&key))?;
        if verified.listing != index.listing {
            return Err("index changed during hydration".into());
        }
        verified.protected
    } else {
        // A merge is in progress: the stages of an unmerged path are the
        // merge's inputs, not a snapshot to verify. Plaintext published here
        // is encrypted again by `git add`, since the paths are protected.
        staged_protected(root, index.merged)?
    };
    let id = transcrypt_v3::config_id(&config);
    let mut pending = Vec::new();
    let mut refresh = Vec::new();
    let mut kept = Vec::new();

    // Decide for every file before writing any. A protected symlink or
    // unreadable file aborts the whole operation. Unmerged files have no
    // staged record of their own; they are decrypted when they hold a
    // record that authenticates at their path (the merge driver's result).
    let targets = protected.iter().map(|e| (e.path.as_slice(), Some(e.oid.as_str())))
        .chain(conflicted.iter().map(|p| (p.as_slice(), None)));
    for (path, oid) in targets {
        let relative = indexed_path(path)?;
        // A deleted (or sparse) file holds nothing to decrypt.
        let Some(target) = find_protected(root, &relative)? else { continue };
        let (worktree, stamp) = target.read()?;
        let object = match oid { Some(oid) => git_blob(root, oid)?, None => Vec::new() };
        // The record this file holds, if any: the staged one, or another
        // that authenticates at this path.
        let is_staged = oid.is_some() && *worktree == object;
        let record: Option<&[u8]> = if is_staged {
            Some(&object)
        } else if record_envelope_ok(&worktree, &id) {
            Some(&worktree)
        } else {
            None
        };
        if let Some(record) = record {
            let plaintext = key.open(path, record)
                .map_err(|e| format!("{}: {e}", String::from_utf8_lossy(path)))?;
            if hydrate_action(&worktree, record, &plaintext) == Ok(HydrateAction::Publish) {
                pending.push((path, relative, stamp, record.to_vec(), is_staged));
                continue;
            }
        }
        if oid.is_some() {
            let plaintext = key.open(path, &object)?;
            if hydrate_action(&worktree, &object, &plaintext) == Ok(HydrateAction::Keep) {
                refresh.push(path.to_vec());
            }
        }
        kept.push(relative);
    }
    // Detect a changed index or public configuration between validation and
    // publication.
    if git(root, &["ls-files", "--stage", "-z"])? != index.listing || load_config(root)? != config {
        return Err("index or public configuration changed during hydration".into());
    }
    let published = pending.len();
    for (path, relative, stamp, record, is_staged) in pending {
        let plaintext = key.open(path, &record)?;
        // `replace` refuses unless the file is still the record checked above.
        open_protected(root, &relative)?.replace(staging, &plaintext, &stamp, key.private())?;
        if is_staged { refresh.push(path.to_vec()); }
    }
    // Private mode: plaintext that Git's checkout wrote follows the umask
    // and may be readable by other users.
    if key.private() {
        for relative in &kept {
            open_protected(root, relative)?.make_private()?;
        }
    }
    // Git's index still caches the size/mtime of the encrypted checkout, and
    // `update-index --refresh` skips files whose size changed. Re-index the
    // files that now hold exactly the staged plaintext (never an edit or a
    // different version, which would stage it) through the clean filter:
    // `update-index -z --stdin` takes raw path bytes, never pathspecs, and
    // without `--add` cannot stage an untracked file. `reindex` verifies that
    // no staged blob or mode changed, even when index != HEAD.
    reindex(root, &index.listing, &refresh)?;
    Ok(published)
}

/// `lock`: replace the plaintext of every worktree of this repository by
/// its committed records, then forget the key (the stored file, or the
/// private agent). Any refusal keeps the key.
pub(crate) fn lock(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    let Some(key) = Key::load(root, &config)? else {
        // No usable key here: nothing can be flushed. Locked means no
        // plaintext is left in any worktree; another worktree on another
        // config may still need the stored key to lock.
        worktree_encrypted(root, &config)
            .map_err(|e| format!("{e}, but there is no key to encrypt it: unlock, then lock"))?;
        others_encrypted(root)?;
        crate::credential::forget(root)?;
        eprintln!("Already locked.");
        return Ok(());
    };
    let bin = env::current_exe().map_err(|_| "cannot locate executable")?;
    for other in other_worktrees(root)? {
        let flushed = std::process::Command::new(&bin).arg("flush").current_dir(&other)
            .stdout(std::process::Stdio::null()).stderr(std::process::Stdio::null()).status()
            .map_err(|e| format!("cannot lock worktree {}: {e}", other.display()))?.success();
        // A worktree on another config cannot be flushed with this key; it
        // is fine if it holds no plaintext.
        let encrypted = || std::process::Command::new(&bin).arg("check-encrypted").current_dir(&other)
            .output().is_ok_and(|out| out.status.success());
        if !flushed && !encrypted() {
            return Err(format!("worktree {} could not be locked (uncommitted changes, or plaintext under \
                another config); the key is kept", other.display()));
        }
    }
    flush(root)?;
    if key.private() {
        crate::session::stop(root, &config)?;
    } else {
        crate::credential::forget(root)?;
    }
    eprintln!("Locked: protected files replaced by their ciphertext and the key forgotten. \
        This does not securely erase earlier plaintext copies.");
    Ok(())
}

/// Refuse unless every other worktree holds no plaintext (each checked in
/// its own process, with its own config).
pub(crate) fn others_encrypted(root: &Path) -> Result<(), String> {
    let bin = env::current_exe().map_err(|_| "cannot locate executable")?;
    for other in other_worktrees(root)? {
        let out = std::process::Command::new(&bin).arg("check-encrypted").current_dir(&other).output()
            .map_err(|e| format!("cannot check worktree {}: {e}", other.display()))?;
        if !out.status.success() {
            return Err(format!("worktree {} still holds plaintext ({}); lock it there first",
                other.display(), String::from_utf8_lossy(&out.stderr).trim().trim_start_matches("transcrypt-v3: ")));
        }
    }
    Ok(())
}

/// The other worktrees of this repository (from `git worktree list`), that
/// still exist on disk.
fn other_worktrees(root: &Path) -> Result<Vec<PathBuf>, String> {
    let listing = String::from_utf8(git(root, &["worktree", "list", "--porcelain"])?)
        .map_err(|_| "worktree paths must be UTF-8")?;
    let this = root.canonicalize().map_err(|_| "cannot resolve the repository root")?;
    let mut others = Vec::new();
    for block in listing.split("\n\n") {
        let mut lines = block.lines();
        let Some(path) = lines.next().and_then(|l| l.strip_prefix("worktree ")) else { continue };
        if block.lines().any(|l| l == "bare") { continue; }
        let path = PathBuf::from(path);
        if path.canonicalize().is_ok_and(|p| p != this) {
            others.push(path);
        }
    }
    Ok(others)
}

/// Replace this worktree's plaintext by the committed records, keeping the
/// key (`lock` forgets it once every worktree is done).
pub(crate) fn flush(root: &Path) -> Result<(), String> {
    let staging = staging_dir(root)?;
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    // Every protected file must match the encrypted index BEFORE any
    // worktree rewrite. If anything is dirty or untracked, keep the key.
    let verified = check_index(root, Some(&key))?;
    untracked_protected(root)?;
    let mut to_flush = Vec::new();
    let mut present = Vec::new();
    for staged in &verified.protected {
        let relative = indexed_path(&staged.path)?;
        // A deleted file holds no plaintext: nothing to flush.
        let Some(target) = find_protected(root, &relative)? else { continue };
        present.push(staged.path.clone());
        let (source, stamp) = target.read()?;
        // The object the index named when it was verified, by object id.
        let object = git_blob(root, &staged.oid)?;
        let resealed = if *source == object { Zeroizing::new(Vec::new()) } else {
            key.clean(&staged.path, &source)?
        };
        match lock_action(&source, &object, &resealed) {
            Ok(LockAction::Keep) => {},
            Ok(LockAction::Flush) => {
                if target.links()? > 1 {
                    eprintln!("warning: {} has other hard links; they keep its plaintext after lock",
                        String::from_utf8_lossy(&staged.path));
                }
                to_flush.push((relative, object, stamp));
            },
            Err(_) => return Err(format!("{} has uncommitted changes; commit or discard them before locking",
                String::from_utf8_lossy(&staged.path))),
        }
    }
    // Write only ciphertext via private staged files and atomic rename. A
    // crash can leave some files flushed and others plaintext; the key is
    // kept until every rename succeeds, and rerunning `lock` resumes
    // (already-flushed files are `LockAction::Keep`). A file changed after it
    // was checked is refused, not overwritten. No secure erasure claim.
    for (relative, object, stamp) in &to_flush {
        open_protected(root, relative)?.replace(&staging, object, stamp, false)?;
    }
    // Refresh Git's cached stat data for the ciphertext now in the worktree
    // (the clean filter returns an authentic record unchanged), so a locked
    // checkout is clean and `git commit -a` does not need the key.
    reindex(root, &verified.listing, &present)?;
    Ok(())
}

/// Refuse if an untracked file is protected: its plaintext would be left
/// behind by `lock`.
fn untracked_protected(root: &Path) -> Result<(), String> {
    let untracked = git(root, &["ls-files", "--others", "-z"])?;
    let paths: Vec<&[u8]> = untracked.split(|b| *b == 0).filter(|p| !p.is_empty()).collect();
    let flags = protected_flags(root, &paths, Attributes::Worktree)?;
    if let Some((path, _)) = paths.iter().zip(flags).find(|(_, p)| *p) {
        return Err(format!("untracked protected file {} holds plaintext; add or remove it first",
            String::from_utf8_lossy(path)));
    }
    Ok(())
}

/// Whether the worktree holds no plaintext secret: every protected tracked
/// file present has the v3 envelope of this config, and no untracked file
/// is protected.
pub(crate) fn worktree_encrypted(root: &Path, config: &[u8]) -> Result<(), String> {
    let id = transcrypt_v3::config_id(config);
    for staged in protected_entries(root, indexed_files(root)?, Attributes::Staged)? {
        if let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? {
            let (contents, _) = target.read()?;
            if !record_envelope_ok(&contents, &id) {
                return Err(format!("{} holds plaintext", String::from_utf8_lossy(&staged.path)));
            }
        }
    }
    untracked_protected(root)
}
