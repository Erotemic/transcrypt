//! The index and worktree lifecycle: `verify-index` and the pre-commit
//! hook, `hydrate`, and `lock` (`flush` per worktree). Every decision to
//! publish, keep or replace bytes is made by the verified core.

use std::{collections::{HashMap, HashSet}, env, fs, io, path::{Path, PathBuf}};
use zeroize::Zeroizing;
use transcrypt_v3_core::{
    entry_check, hydrate_action, is_local_change, is_object_id, is_reserved_path, lock_action, parse_file_header,
    record_envelope_ok, seal_action,
    EntryCheck, HydrateAction, LockAction, SealAction, ATTRIBUTES_NAME,
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

/// One read of the index: its exact listing (`Listing`: bytes, record ends
/// and entries) and, for each entry, whether Git's staged attributes (what the
/// next commit will say) protect it.
struct Snapshot {
    listing: Listing,
    flags: Vec<bool>,
}

impl Snapshot {
    fn read(root: &Path) -> Result<Snapshot, String> {
        Snapshot::of(root, Listing::parse(index_listing(root)?)?)
    }

    /// The snapshot of `listing`, with Git's answer for its own paths.
    fn of(root: &Path, listing: Listing) -> Result<Snapshot, String> {
        let flags = listing_flags(root, &listing, Attributes::Staged)?;
        Ok(Snapshot { listing, flags })
    }

    fn entries(&self) -> &[Staged] {
        self.listing.entries()
    }

    /// The positions of the protected entries, each `Selectable` (the
    /// verified `first_unselectable` decides; `selectable` only words the
    /// refusal).
    fn protected(&self) -> Result<Vec<usize>, String> {
        let first = self.listing.first_unselectable(&self.flags);
        if let Some(entry) = self.entries().get(first) {
            selectable(entry)?;
            return Err(format!("{} is selected for encryption but cannot be protected", entry.name()));
        }
        Ok((0..self.flags.len()).filter(|i| self.flags[*i]).collect())
    }
}

/// A protected entry must be a file Git filters, and not repository metadata.
fn selectable(entry: &Staged) -> Result<(), String> {
    let name = entry.name();
    if is_reserved_path(&entry.path) {
        return Err(format!("{name} is selected for encryption, but v3 never encrypts .gitattributes, \
            .gitmodules or .transcrypt/; narrow the .gitattributes pattern that selects it"));
    }
    if !entry.regular {
        return Err(format!("{name} is selected for encryption but is a symlink or submodule, \
            which Git stores unfiltered; narrow the pattern or replace it by a file"));
    }
    Ok(())
}

/// The protected stage-0 entries of `entries`, by Git's staged attributes,
/// each `selectable`.
pub(crate) fn staged_protected(root: &Path, entries: Vec<Staged>) -> Result<Vec<Staged>, String> {
    let protected = protected_entries(root, entries, Attributes::Staged)?;
    protected.iter().try_for_each(selectable)?;
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
    check_staged(root, &config, Snapshot::read(root)?, &commit_listing(root, "HEAD")?, key, false)
}

/// `check_index` of `snapshot`; with `incremental` (the pre-commit hook),
/// protected entries unchanged since both `HEAD` and `HEAD^1` (*settled*)
/// get the keyless checks only. They are already in history, so
/// authenticating them again on every commit would prevent nothing
/// (`HEAD^1` counts because `--amend` makes it the parent); `verify-index`,
/// `hydrate`, `lock`, merge commits and the audit still authenticate
/// everything. Nothing is settled while an attribute file or the config
/// differs from `HEAD` or `HEAD^1`: a newly selected file was never checked.
fn check_staged(root: &Path, config: &[u8], snapshot: Snapshot, head: &Listing, key: Option<&Key>, incremental: bool)
    -> Result<Verified, String>
{
    let (entries, flags) = (snapshot.entries(), &snapshot.flags);
    match entries.iter().find(|e| e.path == CONFIG_PATH.as_bytes()) {
        Some(e) if e.regular && git_blob(root, &e.oid)? == config => {},
        _ => return Err("staged .transcrypt/config is missing, not a regular file or differs from the worktree \
            (an interrupted `rekey`? `git reset` undoes a staged rekey)".into()),
    }
    let top = entries.iter().find(|e| e.path == ATTRIBUTES_NAME && e.regular).map(|e| e.oid.as_str());
    if !macro_resolves(root, &git_dir(root), top)? {
        return Err(crate::attributes::MACRO_MISSING.into());
    }
    if let Some(problem) = marked_unfiltered(root, &paths_of(entries), Attributes::Staged)? {
        return Err(problem);
    }
    // With `--amend` (and squash/fixup) the commit's parent is `HEAD^`; its
    // files count too, as they do for the audit, which compares with the
    // parent.
    let parent = commit_listing(root, "HEAD^1")?;
    // Whether `HEAD` holds each entry's blob at its path, and (protected
    // entries) `HEAD^1` too: the verified `held_entries`.
    let in_head = snapshot.listing.held_in(&vec![true; entries.len()], head)?;
    let in_parent = snapshot.listing.held_in(flags, &parent)?;
    let protected = snapshot.protected()?;
    let id = transcrypt_rs::config_id(config);
    check_unprotected(root, &id, &snapshot, &in_head, head, &parent)?;
    let same_policy = policy_unchanged(entries, head, &parent);
    // The keyless move check looks blobs up by object id (`blob_elsewhere`).
    let mut ordered: Option<[OrderedListing; 3]> = None;
    for i in protected {
        let staged = &entries[i];
        // Unchanged since `HEAD` and `HEAD^1`: already in history.
        let settled = same_policy && in_head[i] && in_parent[i];
        let record = git_blob(root, &staged.oid)?;
        let name = staged.name();
        match parse_file_header(&record) {
            Err(_) => return Err(format!("staged {name} is not encrypted (was it staged before it was protected?); \
                run `transcrypt-rs protect` or `git add --renormalize -- {name}`")),
            Ok(found) if found != id => return Err(format!("staged {name} is encrypted under another config \
                (cherry-picked or rebased across a rekey?); run `transcrypt-rs reencrypt` with that config's passphrase")),
            Ok(_) => {},
        }
        match (entry_check(key.is_some(), incremental, settled), key) {
            (EntryCheck::Authenticate, Some(key)) => { key.open(&staged.path, &record).map_err(|e| format!("staged \
                {name}: {e}; if it was moved here, `git add --renormalize -- {name}` re-encrypts it from the worktree"))?; },
            // `entry_check` authenticates only with the key; refuse rather than check less.
            (EntryCheck::Authenticate, None) => return Err("internal error: authentication without a key".into()),
            _ if !record_envelope_ok(&record, &id) =>
                return Err(format!("staged {name} is not v3 ciphertext for this repository")),
            // A copy already in history is reported where it was made.
            (EntryCheck::Envelope, _) => {},
            (EntryCheck::EnvelopeNotMoved, _) => {
                let [index_ordered, head_ordered, parent_ordered] = get_or_try_init(&mut ordered, || -> Result<_, String> {
                    Ok([snapshot.listing.ordered()?, head.ordered()?, parent.ordered()?])
                })?;
                if !index_ordered.blob_elsewhere(i, head_ordered, parent_ordered) {
                    continue;
                }
                let other = head.entries().iter().chain(parent.entries()).chain(entries)
                    .find(|e| e.oid == staged.oid && e.path != staged.path).map(Staged::name).unwrap_or_default();
                return Err(format!("staged {name} holds the encrypted {other}: a renamed or copied protected \
                    file must be committed while unlocked, which re-encrypts it for its new name"));
            },
        }
    }
    let Snapshot { listing, flags } = snapshot;
    let (listing, entries) = listing.into_bytes_and_entries();
    let protected = entries.into_iter().zip(flags).filter(|(_, p)| *p).map(|(e, _)| e).collect();
    Ok(Verified { listing, protected })
}

/// The checks of `check_staged` on the unprotected regular entries staged
/// since `HEAD` (`in_head` false): none is a record of this configuration
/// `id`, and none that was a record in `HEAD` (or `HEAD^1`, `parent`) is
/// now claimed by another named filter.
fn check_unprotected(root: &Path, id: &[u8; transcrypt_v3_core::ID_LEN], snapshot: &Snapshot, in_head: &[bool],
    head: &Listing, parent: &Listing) -> Result<(), String>
{
    let (head_oid, parent_oid) = (oids_by_path(head.entries()), oids_by_path(parent.entries()));
    let staged_unprotected = snapshot.entries().iter().zip(&snapshot.flags).zip(in_head)
        .filter(|((e, p), unchanged)| !**p && e.regular && !**unchanged).map(|((e, _), _)| e);
    let mut drifted: Vec<&[u8]> = Vec::new();
    for entry in staged_unprotected {
        let path = entry.path.as_slice();
        if is_record(root, &entry.oid, id)? {
            return Err(format!("{} holds an encrypted record but is not protected (moved to an unprotected \
                name? or a pattern that matches it only case-insensitively: v3 matches case-sensitively, \
                so write it with the file's exact case): nothing would ever decrypt it there. Protect that \
                name, move the file back, or stage its plaintext", String::from_utf8_lossy(path)));
        }
        // Either old blob may be the record: `HEAD^1` is the parent of an
        // amended commit. As strict as the audit: an unreadable one is an
        // error, not a plaintext.
        for old in [head_oid.get(path), parent_oid.get(path)].into_iter().flatten() {
            if is_record(root, old, id)? {
                drifted.push(path);
                break;
            }
        }
    }
    // A file encrypted in `HEAD` that another named filter now claims
    // (`git lfs track` writing `filter=lfs`) silently lost its protection;
    // `unprotect` and `-filter` exclusions are deliberate and allowed.
    let values = filter_values(root, &drifted, Attributes::Staged)?;
    for (path, value) in drifted.iter().zip(&values).filter(|(_, v)| !other_filter(v)) {
        eprintln!("transcrypt-rs: note: {} was encrypted in HEAD and is now staged unencrypted (`filter` is {}): \
            it is no longer selected by .gitattributes", String::from_utf8_lossy(path), String::from_utf8_lossy(value));
    }
    if let Some((path, value)) = drifted.iter().zip(values).find(|(_, v)| other_filter(v)) {
        return Err(format!("{} was encrypted and would now be stored unencrypted for the filter `{}`: a \
            .gitattributes rule (e.g. from `git lfs track`) overrides `transcrypt`. Narrow that rule, or \
            `transcrypt-rs unprotect` the file deliberately", String::from_utf8_lossy(path),
            String::from_utf8_lossy(&value)));
    }
    Ok(())
}

/// Whether the index, `HEAD` and `HEAD^1` (`parent`) have the same attribute
/// files and config. An entry unchanged since `HEAD` and `HEAD^1` was
/// checked when it was committed only if the selection and the config were
/// the same then: entries count as settled only while this holds.
fn policy_unchanged(entries: &[Staged], head: &Listing, parent: &Listing) -> bool {
    let policy = |entries: &[Staged]| -> Vec<(Vec<u8>, String)> {
        entries.iter().filter(|e| is_attributes_file(&e.path) || e.path == CONFIG_PATH.as_bytes())
            .map(|e| (e.path.clone(), e.oid.clone())).collect()
    };
    let staged = policy(entries);
    staged == policy(head.entries()) && staged == policy(parent.entries())
}

/// Each entry's object id, by path.
fn oids_by_path(entries: &[Staged]) -> HashMap<&[u8], &str> {
    entries.iter().map(|e| (e.path.as_slice(), e.oid.as_str())).collect()
}

/// The files of commit `rev`; none when there is no such commit (`HEAD`
/// before the first commit, `HEAD^1` of a root commit).
pub(crate) fn commit_files(root: &Path, rev: &str) -> Result<Vec<Staged>, String> {
    Ok(commit_listing(root, rev)?.into_entries())
}

/// `commit_files`, as a `Listing`. `rev` is resolved once, and the tree of
/// exactly that commit is listed: a concurrent commit cannot make the
/// listing another commit's than the one found.
pub(crate) fn commit_listing(root: &Path, rev: &str) -> Result<Listing, String> {
    match resolve_commit(root, rev)? {
        Some(id) => tree_listing(root, &id),
        None => Ok(Listing::empty()),
    }
}

/// The pseudo-refs naming the commit a cherry-pick, revert or rebase step
/// is bringing in.
const SEQUENCER_HEADS: [&str; 3] = ["CHERRY_PICK_HEAD", "REVERT_HEAD", "REBASE_HEAD"];
/// The directories of a rebase or `git am` in progress.
const REBASE_DIRS: [&str; 2] = ["rebase-merge", "rebase-apply"];

/// Every (path, blob) of the commits a merge, cherry-pick, revert or rebase
/// is bringing in, as one listing: index content equal to one of them came
/// from a commit and is checked, never repaired. `None` when they are not
/// known, and then nothing is repaired: a rebase or `git am` without a
/// known commit, or sequencing state that is present but unreadable or
/// malformed (never taken for "no commit is coming in").
fn incoming(root: &Path) -> Result<Option<Listing>, String> {
    let git_dir = git_dir(root);
    let mut commits = Vec::new();
    match fs::read(git_dir.join("MERGE_HEAD")) {
        Ok(text) => for line in text.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
            if !is_object_id(line) { return Ok(None); }
            commits.push(String::from_utf8_lossy(line).into_owned());
        },
        Err(e) if e.kind() == io::ErrorKind::NotFound => {},
        Err(_) => return Ok(None),
    }
    for name in SEQUENCER_HEADS {
        match resolve_commit(root, name)? {
            Some(id) => commits.push(id),
            // Present, yet naming no commit.
            None if fs::symlink_metadata(git_dir.join(name)).is_ok() => return Ok(None),
            None => {},
        }
    }
    if commits.is_empty() && REBASE_DIRS.iter().any(|dir| git_dir.join(dir).exists()) {
        return Ok(None);
    }
    let trees = commits.iter().map(|commit| tree_listing(root, commit)).collect::<Result<Vec<_>, _>>()?;
    Ok(Some(Listing::merge(trees)?))
}

/// A commit without `.transcrypt/config` (a branch from before `init`):
/// the hooks accept exactly what the audit does, which is anything that
/// protects no file. Returns whether the index is such a commit.
fn configless(snapshot: &Snapshot) -> Result<bool, String> {
    if snapshot.entries().iter().any(|e| e.path == CONFIG_PATH.as_bytes()) { return Ok(false); }
    if let Some(&first) = snapshot.protected()?.first() {
        return Err(format!("{} is protected, but this commit has no .transcrypt/config: it would be \
            stored unencrypted; check out .transcrypt/ from a branch that uses v3",
            snapshot.entries()[first].name()));
    }
    Ok(true)
}

/// `verify-index`, the read-only check, and (with `seal`) the pre-commit
/// hook, which first encrypts what ordinary Git commands stage without the
/// filter (`seal_staged`). Locked, it checks the keyless envelopes, which
/// still rejects any plaintext.
fn verify(root: &Path, seal: bool) -> Result<(), String> {
    let mut snapshot = Snapshot::read(root)?;
    if configless(&snapshot)? { return Ok(()); }
    let config = load_config(root)?;
    let key = Key::load(root, &config)?;
    let head = commit_listing(root, "HEAD")?;
    if let Some(key) = key.as_ref().filter(|_| seal) {
        // Sealing replaced index entries: check the index it left.
        if seal_snapshot(root, key, &[], &snapshot, &head)? > 0 {
            snapshot = Snapshot::read(root)?;
        }
    }
    check_staged(root, &config, snapshot, &head, key.as_ref(), seal)?;
    if key.is_none() {
        eprintln!("transcrypt-rs: locked; checked staged record envelopes only");
    }
    Ok(())
}

/// `verify-index`.
pub(crate) fn verify_index_command(root: &Path) -> Result<(), String> {
    verify(root, false)
}

/// The pre-commit hook.
pub(crate) fn pre_commit(root: &Path) -> Result<(), String> {
    verify(root, true)?;
    if let Some(file) = crate::attributes::filter_overrides(root).first() {
        eprintln!("transcrypt-rs: warning: {file} sets `filter`, which can unprotect files that \
            .gitattributes protects; see `transcrypt-rs doctor`");
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
    seal_snapshot(root, key, force, &Snapshot::read(root)?, &commit_listing(root, "HEAD")?)
}

fn seal_snapshot(root: &Path, key: &Key, force: &[Vec<u8>], snapshot: &Snapshot, head: &Listing)
    -> Result<usize, String>
{
    let protected = snapshot.protected()?;
    // The decision's inputs are verified functions of the snapshots:
    // whether `HEAD` and the incoming commits hold each protected entry
    // (`held_entries`), local changes (`is_local_change`) and move sources
    // (`next_move_source`).
    let in_head = snapshot.listing.held_in(&snapshot.flags, head)?;
    // Only a changed entry can be a local change: skip looking for commits
    // being brought in (three Git commands) on most commits.
    let incoming = if protected.iter().any(|i| !in_head[*i]) { incoming(root)? } else { None };
    let in_incoming = match &incoming {
        Some(files) => snapshot.listing.held_in(&snapshot.flags, files)?,
        None => vec![false; snapshot.flags.len()],
    };
    let force: HashSet<&[u8]> = force.iter().map(Vec::as_slice).collect();
    let mut update = IndexUpdate::new(root, Blobs::Records);
    // `HEAD` by object id, for move sources; only when a record moved.
    let mut head_ordered: Option<OrderedListing> = None;
    for i in protected {
        let staged = &snapshot.entries()[i];
        let mut evidence = RepairEvidence {
            in_head: in_head[i],
            incoming_known: incoming.is_some(),
            in_incoming: in_incoming[i],
            forced: force.contains(staged.path.as_slice()),
            // Until the blob is read: assume a record, which forcing never repairs.
            envelope: true,
        };
        // `seal_action` never repairs a non-local entry; skip decrypting it
        // here (`check_index` verifies it right after).
        if !evidence.local_change() && !evidence.forced { continue; }
        let record = git_blob(root, &staged.oid).map_err(|e| format!("{}: {e}", staged.name()))?;
        let opens = key.open(&staged.path, &record).is_ok();
        evidence.envelope = parse_file_header(&record).is_ok();
        let (envelope, local) = (evidence.envelope, evidence.local_change());
        let moved = if opens || !envelope { None } else {
            let head = get_or_try_init(&mut head_ordered, || head.ordered())?;
            open_moved(key, &snapshot.listing, i, head, &record)
        };
        let name = staged.name().into_owned();
        // The verified core decides.
        let plaintext: Zeroizing<Vec<u8>> = match seal_action(opens, local, envelope, moved.is_some()) {
            SealAction::Keep | SealAction::Leave => continue,
            SealAction::Seal => {
                eprintln!("transcrypt-rs: encrypting {name}, which was staged unencrypted");
                Zeroizing::new(record)
            },
            SealAction::Rebind => {
                let Some((source, plaintext)) = moved else { continue };
                eprintln!("transcrypt-rs: re-encrypting {name} for its new name (it was {})",
                    String::from_utf8_lossy(source));
                plaintext
            },
        };
        update.add(&staged.mode, &staged.path, &key.clean(&staged.path, &plaintext)?)?;
    }
    let count = update.len();
    update.apply(&[])?;
    Ok(count)
}

/// What the pre-commit hook knows about one staged protected entry, for the
/// verified `is_local_change`: a change the user made (not in `HEAD` at its
/// path, the commits being brought in known and not holding it either), or
/// plaintext (no `envelope`) that `protect` `forced`.
struct RepairEvidence {
    in_head: bool,
    incoming_known: bool,
    in_incoming: bool,
    forced: bool,
    envelope: bool,
}

impl RepairEvidence {
    fn local_change(&self) -> bool {
        is_local_change(self.in_head, self.incoming_known, self.in_incoming, self.forced, self.envelope)
    }
}

/// The first `HEAD` path that entry `i` of `index` may have been moved from
/// (`OrderedListing::move_sources`) at which `record` opens, with its
/// plaintext.
fn open_moved<'a>(key: &Key, index: &Listing, i: usize, head: &OrderedListing<'a>, record: &[u8])
    -> Option<(&'a [u8], Zeroizing<Vec<u8>>)>
{
    head.move_sources(index, i)
        .find_map(|source| key.open(&source.path, record).ok().map(|plaintext| (source.path.as_slice(), plaintext)))
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
    let index = Listing::parse(index_listing(root)?)?;
    let head = commit_listing(root, "HEAD")?;
    let head = head.ordered()?;
    index.entries().iter().position(|e| e.path == staged.path && e.oid == staged.oid)
        .and_then(|i| open_moved(key, &index, i, &head, &record)).map(|(_, plaintext)| plaintext)
        .ok_or_else(|| format!("{}: {error}", staged.name()))
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
        Ok(n) => eprintln!("transcrypt-rs: decrypted {n} file(s) with mode {:04o}.", crate::modes::PRIVATE_FILE),
        Err(e) => eprintln!("transcrypt-rs: automatic decryption skipped: {e}\n\
            Inspect with `transcrypt-rs status`, then run `transcrypt-rs hydrate`."),
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

/// A file `hydrate` decided to decrypt: replaced by `plaintext` only if it
/// still has `stamp`, then re-indexed if it held the `staged` record.
struct Publish<'a> {
    path: &'a [u8],
    relative: PathBuf,
    stamp: crate::fsat::Stamp,
    plaintext: Zeroizing<Vec<u8>>,
    staged: bool,
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
        let snapshot = Snapshot::of(root, Listing::parse(index.listing.clone())?)?;
        check_staged(root, &config, snapshot, &commit_listing(root, "HEAD")?, Some(&key), false)?.protected
    } else {
        // A merge is in progress: the stages of an unmerged path are the
        // merge's inputs, not a snapshot to verify. Plaintext published here
        // is encrypted again by `git add`, since the paths are protected.
        staged_protected(root, index.merged)?
    };
    let id = transcrypt_rs::config_id(&config);
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
        let object = oid.map(|oid| git_blob(root, oid)).transpose()?;
        // The record this file holds, if any: the staged one, or another
        // that authenticates at this path.
        let staged = object.as_ref().is_some_and(|object| *worktree == *object);
        let record: Option<&[u8]> = match &object {
            Some(object) if staged => Some(object),
            _ if record_envelope_ok(&worktree, &id) => Some(&worktree),
            _ => None,
        };
        if let Some(record) = record {
            let plaintext = key.open(path, record)
                .map_err(|e| format!("{}: {e}", String::from_utf8_lossy(path)))?;
            if hydrate_action(&worktree, record, &plaintext) == Ok(HydrateAction::Publish) {
                pending.push(Publish { path, relative, stamp, plaintext, staged });
                continue;
            }
        }
        if let Some(object) = &object {
            let plaintext = key.open(path, object)?;
            if hydrate_action(&worktree, object, &plaintext) == Ok(HydrateAction::Keep) {
                refresh.push(path.to_vec());
            }
        }
        kept.push(relative);
    }
    // Detect a changed index or public configuration between validation and
    // publication.
    if index_listing(root)? != index.listing || load_config(root)? != config {
        return Err("index or public configuration changed during hydration".into());
    }
    let published = pending.len();
    for Publish { path, relative, stamp, plaintext, staged } in pending {
        // `replace` refuses unless the file is still the record checked above.
        open_protected(root, &relative)?.replace(staging, &plaintext, &stamp, key.private())?;
        if staged { refresh.push(path.to_vec()); }
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
    for other in other_worktrees(root)? {
        let flushed = run_in(&other, "flush")
            .map_err(|e| format!("cannot lock worktree {}: {e}", other.display()))?.status.success();
        // A worktree on another config cannot be flushed with this key; it
        // is fine if it holds no plaintext.
        if !flushed && !run_in(&other, "check-encrypted").is_ok_and(|f| f.status.success()) {
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
    for other in other_worktrees(root)? {
        let Finished { status, errors, .. } = run_in(&other, "check-encrypted")
            .map_err(|e| format!("cannot check worktree {}: {e}", other.display()))?;
        if !status.success() {
            return Err(format!("worktree {} still holds plaintext ({}); lock it there first",
                other.display(), String::from_utf8_lossy(&errors).trim().trim_start_matches("transcrypt-rs: ")));
        }
    }
    Ok(())
}

/// Run this executable's `command` in the worktree `dir`, bounded.
fn run_in(dir: &Path, command: &str) -> Result<Finished, String> {
    let mut child = std::process::Command::new(env::current_exe().map_err(|_| "cannot locate executable")?);
    child.arg(command).current_dir(dir);
    run_bounded_status(child, None, SHORT_OUTPUT_LIMIT)
}

/// The other worktrees of this repository (`git worktree list`), except
/// those Git found gone (`prunable`). One that exists but cannot be
/// resolved is an error, never skipped: `lock` must not forget the key
/// while an unchecked worktree may still hold plaintext.
fn other_worktrees(root: &Path) -> Result<Vec<PathBuf>, String> {
    let this = root.canonicalize().map_err(|_| "cannot resolve the repository root")?;
    let mut others = Vec::new();
    for worktree in worktrees(root)? {
        if worktree.bare || worktree.prunable { continue; }
        let path = worktree.path.canonicalize()
            .map_err(|e| format!("cannot inspect worktree {}: {e}", worktree.path.display()))?;
        if path != this { others.push(worktree.path); }
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
                        staged.name());
                }
                to_flush.push((relative, object, stamp));
            },
            Err(_) => return Err(format!("{} has uncommitted changes; commit or discard them before locking",
                staged.name())),
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
/// behind by `lock`. Ignored files count too (no `--exclude-standard`, unlike
/// `status`): an ignored protected file, such as a `.env`, holds plaintext all
/// the same.
fn untracked_protected(root: &Path) -> Result<(), String> {
    let untracked = git(root, &["ls-files", "--others", "-z"])?;
    let paths = git_records(&untracked)?;
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
    let id = transcrypt_rs::config_id(config);
    for staged in protected_entries(root, indexed_files(root)?, Attributes::Staged)? {
        if let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? {
            let (contents, _) = target.read()?;
            if !record_envelope_ok(&contents, &id) {
                return Err(format!("{} holds plaintext", staged.name()));
            }
        }
    }
    untracked_protected(root)
}
