//! The index and worktree lifecycle: `verify-index` and the pre-commit
//! hook, `hydrate`, and `lock` (`flush` per worktree). Every decision to
//! publish, keep or replace bytes is made by the verified core.

use std::{cell::RefCell, collections::{HashMap, HashSet}, env, fs, io, path::{Path, PathBuf}};
use zeroize::Zeroizing;
use transcrypt_v3_core::{
    hydrate_action, is_reserved_path, lock_action, needs_record, parse_file_header, record_envelope_ok, repair_plan,
    HydrateAction, LockAction, RecordClass, RepairPlan, StagedEvidence, StagedRefusal, ATTRIBUTES_NAME, ID_LEN,
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
    fn read(repo: &Repository) -> Result<Snapshot, String> {
        Snapshot::of(repo, Listing::parse(index_listing(repo)?)?)
    }

    /// The snapshot of `listing`, with Git's answer for its own paths.
    fn of(repo: &Repository, listing: Listing) -> Result<Snapshot, String> {
        let flags = listing_flags(repo, &listing, Attributes::Staged)?;
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
    if !entry.regular() {
        return Err(format!("{name} is selected for encryption but is a symlink or submodule, \
            which Git stores unfiltered; narrow the pattern or replace it by a file"));
    }
    Ok(())
}

/// The protected stage-0 entries of `entries`, by Git's staged attributes,
/// each `selectable`.
pub(crate) fn staged_protected(repo: &Repository, entries: Vec<Staged>) -> Result<Vec<Staged>, String> {
    let protected = protected_entries(repo, entries, Attributes::Staged)?;
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
///   would be committed where nothing ever decrypts it;
/// - with the key, every unprotected file `HEAD` holds that is a record of
///   this configuration opens at its path (a forgery left at an unprotected
///   name is refused before any attribute source can protect it).
pub(crate) fn check_index(repo: &Repository, key: Option<&Key>) -> Result<Verified, String> {
    let config = load_config(repo)?;
    check_staged(repo, &config, Snapshot::read(repo)?, &commit_listing(repo, "HEAD")?, key, false)
}

/// `check_index` of `snapshot`; with `incremental` (the pre-commit hook),
/// entries `HEAD` holds are trusted from history while the attribute files
/// and the config are those of `HEAD` and `HEAD^1` (the guard): a protected
/// entry unchanged since both (*settled*) gets the keyless checks only, and
/// an unprotected file `HEAD` holds is not read at all. Authenticating them
/// again on every commit would prevent nothing (`HEAD^1` counts because
/// `--amend` makes it the parent); `verify-index`, `lock`, `rekey`, merge
/// commits and the audit still authenticate everything. The verified core
/// decides each entry's check (`staged_check`) and whether it passes
/// (`staged_verdict`), for every entry in order (`index_verdict`); this
/// answers what the checks ask (`IndexEvidence`).
fn check_staged(repo: &Repository, config: &[u8], snapshot: Snapshot, head: &Listing, key: Option<&Key>, incremental: bool)
    -> Result<Verified, String>
{
    let (entries, flags) = (snapshot.entries(), &snapshot.flags);
    match entries.iter().find(|e| e.path == CONFIG_PATH.as_bytes()) {
        Some(e) if e.regular() && git_blob(repo, &e.oid)? == config => {},
        _ => return Err("staged .transcrypt/config is missing, not a regular file or differs from the worktree \
            (an interrupted `rekey`? `git reset` undoes a staged rekey)".into()),
    }
    let top = entries.iter().find(|e| e.path == ATTRIBUTES_NAME && e.regular()).map(|e| &e.oid);
    if !macro_resolves(repo, top)? {
        return Err(crate::attributes::MACRO_MISSING.into());
    }
    if let Some(problem) = marked_unfiltered(repo, &paths_of(entries), Attributes::Staged)? {
        return Err(problem);
    }
    // With `--amend` (and squash/fixup) the commit's parent is `HEAD^`; its
    // files count too, as they do for the audit, which compares with the
    // parent.
    let parent = commit_listing(repo, "HEAD^1")?;
    // Whether `HEAD` holds each entry's exact record (mode, blob and path),
    // and (protected entries) `HEAD^1` too: the verified `held_records`. A
    // symlink of `HEAD` staged as a file with the same blob is not held: it
    // was never checked as a file.
    let in_head = snapshot.listing.records_in(&vec![true; entries.len()], head)?;
    let in_parent = snapshot.listing.records_in(flags, &parent)?;
    snapshot.protected()?;
    let id = transcrypt_rs::config_id(config);
    // Nothing is trusted from `HEAD` unless the attribute files and the
    // config are the same in the index, `HEAD` and `HEAD^1` (the verified
    // `policy_unchanged`). The config is what the history's records were
    // checked under; the attribute files are defence in depth.
    let guard = snapshot.listing.policy_unchanged(head, &parent);
    // The keyless move check looks blobs up by object id (`blob_elsewhere`),
    // in orders built at most once.
    let mut evidence = IndexEvidence {
        repo, key, id: &id, index: &snapshot.listing, head, parent: &parent,
        ordered: RefCell::new(None), blob: Vec::new(), read: None, unopened: RefCell::new(None),
        failure: RefCell::new(None),
    };
    // Every entry, in order, by the verified `index_verdict`.
    let verdict = snapshot.listing.index_verdict(&mut evidence, flags, &in_head, &in_parent, key.is_some(), incremental,
        guard, &id);
    if let Err((i, refusal)) = verdict {
        return Err(refusal_message(refusal, &evidence, &entries[i]));
    }
    check_drift(repo, &id, &snapshot, &in_head, head, &parent)?;
    let Snapshot { listing, flags } = snapshot;
    let (listing, entries) = listing.into_bytes_and_entries();
    let protected = entries.into_iter().zip(flags).filter(|(_, p)| *p).map(|(e, _)| e).collect();
    Ok(Verified { listing, protected })
}

/// The adapter's answers about the entries of the index (`index`) for the
/// verified `index_verdict` and `staged_verdict`, each about entry `i`'s own
/// blob (by object id) and path, computed only when asked.
struct IndexEvidence<'a, 'l> {
    repo: &'a Repository,
    key: Option<&'a Key>,
    id: &'a [u8; ID_LEN],
    index: &'l Listing,
    head: &'l Listing,
    parent: &'l Listing,
    ordered: RefCell<Option<[OrderedListing<'l>; 3]>>,
    /// The blob `read` read last, and the entry it is the blob of.
    blob: Vec<u8>,
    read: Option<usize>,
    /// Why the blob did not open, for the message.
    unopened: RefCell<Option<String>>,
    /// Why an answer could not be found (a failed read), for the message.
    failure: RefCell<Option<String>>,
}

impl IndexEvidence<'_, '_> {
    /// The answer `find` gives; if it fails, `None`, with the failure kept.
    fn answer(&self, find: impl FnOnce() -> Result<bool, String>) -> Option<bool> {
        find().map_err(|e| self.failure.replace(Some(e))).ok()
    }

    fn entry(&self, i: usize) -> &Staged {
        &self.index.entries()[i]
    }
}

impl StagedEvidence for IndexEvidence<'_, '_> {
    /// The blob by its object id.
    fn read(&mut self, i: usize) -> bool {
        match git_blob(self.repo, &self.entry(i).oid) {
            Ok(blob) => {
                self.blob = blob;
                self.read = Some(i);
                true
            },
            Err(e) => {
                self.failure.replace(Some(e));
                false
            },
        }
    }

    fn blob(&self) -> &[u8] {
        &self.blob
    }

    /// Its size and first bytes, decided by `record_envelope_prefix_ok`.
    fn is_record(&self, i: usize) -> Option<bool> {
        self.answer(|| is_record(self.repo, &self.entry(i).oid, self.id))
    }

    /// `Key::open` at the entry's path: `open_record` with the stored key,
    /// or the agent's.
    fn opens(&self, i: usize) -> Option<bool> {
        let Some(key) = self.key else { return Some(false) };
        let staged = self.entry(i);
        let read;
        let record = if self.read == Some(i) {
            &self.blob
        } else {
            match git_blob(self.repo, &staged.oid) {
                Ok(blob) => { read = blob; &read },
                Err(e) => return self.answer(|| Err(e)),
            }
        };
        match key.open(&staged.path, record) {
            Ok(_) => Some(true),
            Err(e) => {
                self.unopened.replace(Some(e));
                Some(false)
            },
        }
    }

    /// The verified `blob_elsewhere`.
    fn elsewhere(&self, i: usize) -> Option<bool> {
        self.answer(|| {
            let mut ordered = self.ordered.borrow_mut();
            let [index, head, parent] = get_or_try_init(&mut ordered, || -> Result<_, String> {
                Ok([self.index.ordered()?, self.head.ordered()?, self.parent.ordered()?])
            })?;
            Ok(index.blob_elsewhere(i, head, parent))
        })
    }
}

/// The message for the verified refusal of entry `staged` of `evidence`.
fn refusal_message(refusal: StagedRefusal, evidence: &IndexEvidence, staged: &Staged) -> String {
    let name = staged.name();
    let unopened = || evidence.unopened.take().unwrap_or_default();
    match refusal {
        StagedRefusal::Plaintext => format!("staged {name} is not encrypted (was it staged before it was protected?); \
            run `transcrypt-rs protect` or `git add --renormalize -- {name}`"),
        StagedRefusal::OtherConfig => format!("staged {name} is encrypted under another config (cherry-picked or \
            rebased across a rekey?); run `transcrypt-rs reencrypt` with that config's passphrase"),
        StagedRefusal::Envelope => format!("staged {name} is not v3 ciphertext for this repository"),
        StagedRefusal::Authentication => format!("staged {name}: {}; if it was moved here, `git add --renormalize \
            -- {name}` re-encrypts it from the worktree", unopened()),
        StagedRefusal::Moved => {
            let other = evidence.head.entries().iter().chain(evidence.parent.entries()).chain(evidence.index.entries())
                .find(|e| e.oid == staged.oid && e.path != staged.path).map(Staged::name).unwrap_or_default();
            format!("staged {name} holds the encrypted {other}: a renamed or copied protected file must be \
                committed while unlocked, which re-encrypts it for its new name")
        },
        StagedRefusal::UnprotectedRecord => format!("{name} holds an encrypted record but is not protected (moved \
            to an unprotected name? or a pattern that matches it only case-insensitively: v3 matches \
            case-sensitively, so write it with the file's exact case): nothing would ever decrypt it there. \
            Protect that name, move the file back, or stage its plaintext"),
        StagedRefusal::UnprotectedForgery => format!("{name} is not protected but holds a record of this \
            configuration that does not open there ({}): a record moved without re-encryption, or a forgery, \
            which an attribute change would protect unauthenticated. Remove it, or stage its plaintext",
            unopened()),
        StagedRefusal::Unanswered => format!("staged {name}: {}",
            evidence.failure.take().unwrap_or_else(|| "cannot be read".into())),
    }
}

/// The unprotected regular entries staged since `HEAD` (`in_head` false):
/// none that was a record in `HEAD` (or `HEAD^1`, `parent`) is now claimed by
/// another named filter (configuration `id`). The final check already
/// refused any that is a record itself.
fn check_drift(repo: &Repository, id: &[u8; ID_LEN], snapshot: &Snapshot, in_head: &[bool],
    head: &Listing, parent: &Listing) -> Result<(), String>
{
    let (head_oid, parent_oid) = (oids_by_path(head.entries()), oids_by_path(parent.entries()));
    let staged_unprotected = snapshot.entries().iter().zip(&snapshot.flags).zip(in_head)
        .filter(|((e, p), unchanged)| !**p && e.regular() && !**unchanged).map(|((e, _), _)| e);
    let mut drifted: Vec<&[u8]> = Vec::new();
    for entry in staged_unprotected {
        let path = entry.path.as_slice();
        // Either old blob may be the record: `HEAD^1` is the parent of an
        // amended commit. As strict as the audit: an unreadable one is an
        // error, not a plaintext.
        for old in [head_oid.get(path), parent_oid.get(path)].into_iter().flatten() {
            if is_record(repo, old, id)? {
                drifted.push(path);
                break;
            }
        }
    }
    // A file encrypted in `HEAD` that another named filter now claims
    // (`git lfs track` writing `filter=lfs`) silently lost its protection;
    // `unprotect` and `-filter` exclusions are deliberate and allowed.
    let values = filter_values(repo, &drifted, Attributes::Staged)?;
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

/// Each entry's object id, by path.
fn oids_by_path(entries: &[Staged]) -> HashMap<&[u8], &ObjectId> {
    entries.iter().map(|e| (e.path.as_slice(), &e.oid)).collect()
}

/// The files of commit `rev`; none when there is no such commit (`HEAD`
/// before the first commit, `HEAD^1` of a root commit).
pub(crate) fn commit_files(repo: &Repository, rev: &str) -> Result<Vec<Staged>, String> {
    Ok(commit_listing(repo, rev)?.into_entries())
}

/// `commit_files`, as a `Listing`. `rev` is resolved once, and the tree of
/// exactly that commit is listed: a concurrent commit cannot make the
/// listing another commit's than the one found.
pub(crate) fn commit_listing(repo: &Repository, rev: &str) -> Result<Listing, String> {
    match resolve_commit(repo, rev)? {
        Some(id) => tree_listing(repo, id.as_str()),
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
fn incoming(repo: &Repository) -> Result<Option<Listing>, String> {
    let git_dir = repo.git_dir();
    let mut commits = Vec::new();
    match fs::read(git_dir.join("MERGE_HEAD")) {
        Ok(text) => for line in text.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
            let Some(id) = ObjectId::new(line) else { return Ok(None) };
            commits.push(id);
        },
        Err(e) if e.kind() == io::ErrorKind::NotFound => {},
        Err(_) => return Ok(None),
    }
    for name in SEQUENCER_HEADS {
        match resolve_commit(repo, name)? {
            Some(id) => commits.push(id),
            // Present, yet naming no commit.
            None if fs::symlink_metadata(git_dir.join(name)).is_ok() => return Ok(None),
            None => {},
        }
    }
    if commits.is_empty() && REBASE_DIRS.iter().any(|dir| git_dir.join(dir).exists()) {
        return Ok(None);
    }
    let trees = commits.iter().map(|commit| tree_listing(repo, commit.as_str())).collect::<Result<Vec<_>, _>>()?;
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
fn verify(repo: &Repository, seal: bool) -> Result<(), String> {
    let mut snapshot = Snapshot::read(repo)?;
    if configless(&snapshot)? { return Ok(()); }
    let config = load_config(repo)?;
    let key = Key::load(repo, &config)?;
    let head = commit_listing(repo, "HEAD")?;
    if let Some(key) = key.as_ref().filter(|_| seal) {
        // Sealing replaced index entries: check the index it left.
        if seal_snapshot(repo, key, &[], &snapshot, &head)? > 0 {
            snapshot = Snapshot::read(repo)?;
        }
    }
    check_staged(repo, &config, snapshot, &head, key.as_ref(), seal)?;
    if key.is_none() {
        eprintln!("transcrypt-rs: locked; checked staged record envelopes only, which does not authenticate \
            them (unlock to authenticate)");
    }
    Ok(())
}

/// `verify-index`.
pub(crate) fn verify_index_command(repo: &Repository) -> Result<(), String> {
    verify(repo, false)
}

/// The pre-commit hook.
pub(crate) fn pre_commit(repo: &Repository) -> Result<(), String> {
    verify(repo, true)?;
    if let Some(file) = crate::attributes::filter_overrides(repo).first() {
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
/// Only local changes are repaired (the verified `repair_plan` decides from
/// the entry's `Provenance` and its `RecordClass`): an entry equal to
/// `HEAD`'s, or equal to a file of a commit being merged, picked, reverted
/// or rebased, came from a commit, and re-encrypting it would turn a hostile
/// commit's moved or plaintext content into genuine records; `check_index`
/// refuses those instead. `force` lists paths whose plaintext is sealed even
/// when unchanged from `HEAD` (`protect` selecting files committed before
/// they were protected). Returns how many entries were sealed.
pub(crate) fn seal_staged(repo: &Repository, key: &Key, force: &[Vec<u8>]) -> Result<usize, String> {
    seal_snapshot(repo, key, force, &Snapshot::read(repo)?, &commit_listing(repo, "HEAD")?)
}

fn seal_snapshot(repo: &Repository, key: &Key, force: &[Vec<u8>], snapshot: &Snapshot, head: &Listing)
    -> Result<usize, String>
{
    let protected = snapshot.protected()?;
    // Only an entry `HEAD` does not hold can be the user's change: skip
    // looking for commits being brought in (three Git commands) on most
    // commits. `None` (not known) is safe: nothing it would decide is local.
    let in_head = snapshot.listing.held_in(&snapshot.flags, head)?;
    let incoming = if protected.iter().any(|i| !in_head[*i]) { incoming(repo)? } else { None };
    let force: HashSet<&[u8]> = force.iter().map(Vec::as_slice).collect();
    let mut update = IndexUpdate::new(repo, Blobs::Records);
    // `HEAD` by object id, for move sources; only when a record moved.
    let mut head_ordered: Option<OrderedListing> = None;
    for i in protected {
        let staged = &snapshot.entries()[i];
        // The verified core decides where the content came from, and whether
        // anything about its blob could make it repaired; the blob of an
        // entry that cannot be is not read (`check_index` verifies it right
        // after).
        let provenance = snapshot.listing.provenance(i, head, incoming.as_ref(),
            force.contains(staged.path.as_slice()));
        if !needs_record(provenance) { continue; }
        let record = git_blob(repo, &staged.oid).map_err(|e| format!("{}: {e}", staged.name()))?;
        let Classified { class, moved } = classify(key, &snapshot.listing, i, head, &mut head_ordered, staged, &record)?;
        let name = staged.name().into_owned();
        // The verified core decides.
        let plaintext: Zeroizing<Vec<u8>> = match repair_plan(provenance, class) {
            RepairPlan::Keep | RepairPlan::Leave(_) => continue,
            RepairPlan::Seal => {
                eprintln!("transcrypt-rs: encrypting {name}, which was staged unencrypted");
                Zeroizing::new(record)
            },
            RepairPlan::Rebind(source) => {
                let (Some(plaintext), Some(source)) = (moved, head.entries().get(source)) else { continue };
                eprintln!("transcrypt-rs: re-encrypting {name} for its new name (it was {})",
                    String::from_utf8_lossy(&source.path));
                plaintext
            },
        };
        update.add(staged.mode, &staged.path, &key.clean(&staged.path, &plaintext)?)?;
    }
    let count = update.len();
    update.apply(&[])?;
    Ok(count)
}

/// A staged blob's `RecordClass`, with the plaintext of a record moved
/// here (`MovedFrom`).
struct Classified {
    class: RecordClass,
    moved: Option<Zeroizing<Vec<u8>>>,
}

/// What the staged blob `record` of protected entry `i` of `index` is, for
/// the verified `repair_plan`: it opens at its own path; it has no v3
/// envelope; it opens at the first `HEAD` path it may have been moved from
/// (`open_moved`), returned with that plaintext; or none of these. `HEAD`'s
/// object order is computed into `head_ordered` the first time it is needed.
fn classify<'h>(key: &Key, index: &Listing, i: usize, head: &'h Listing,
    head_ordered: &mut Option<OrderedListing<'h>>, staged: &Staged, record: &[u8])
    -> Result<Classified, String>
{
    let only = |class| Ok(Classified { class, moved: None });
    if key.open(&staged.path, record).is_ok() {
        return only(RecordClass::OpensHere);
    }
    if parse_file_header(record).is_err() {
        return only(RecordClass::Plaintext);
    }
    let head = get_or_try_init(head_ordered, || head.ordered())?;
    match open_moved(key, index, i, head, record) {
        Some((source, plaintext)) => Ok(Classified { class: RecordClass::MovedFrom(source), moved: Some(plaintext) }),
        None => only(RecordClass::Unusable),
    }
}

/// The first `HEAD` entry that entry `i` of `index` may have been moved from
/// (`OrderedListing::move_sources`) at whose path `record` opens: its
/// position in `HEAD`, and the plaintext.
fn open_moved(key: &Key, index: &Listing, i: usize, head: &OrderedListing, record: &[u8])
    -> Option<(usize, Zeroizing<Vec<u8>>)>
{
    head.move_sources(index, i)
        .find_map(|(j, source)| key.open(&source.path, record).ok().map(|plaintext| (j, plaintext)))
}

/// The plaintext of a staged protected record: opened at its own path, or,
/// for a record moved there by a local `git mv`, at the `HEAD` path it came
/// from (whose index entry is gone or replaced).
pub(crate) fn open_staged(repo: &Repository, key: &Key, staged: &Staged) -> Result<Zeroizing<Vec<u8>>, String> {
    let record = git_blob(repo, &staged.oid)?;
    let error = match key.open(&staged.path, &record) {
        Ok(plaintext) => return Ok(plaintext),
        Err(e) => e,
    };
    let index = Listing::parse(index_listing(repo)?)?;
    let head = commit_listing(repo, "HEAD")?;
    let head = head.ordered()?;
    index.entries().iter().position(|e| e.path == staged.path && e.oid == staged.oid)
        .and_then(|i| open_moved(key, &index, i, &head, &record)).map(|(_, plaintext)| plaintext)
        .ok_or_else(|| format!("{}: {error}", staged.name()))
}

/// Run from the post-checkout, post-merge and post-rewrite hooks. Only the
/// private mode needs it (its smudge filter leaves ciphertext when Git's
/// umask would expose plaintext); it never fails the finished Git command.
pub(crate) fn auto_hydrate(repo: &Repository) -> Result<(), String> {
    let Ok(config) = load_config(repo) else { return Ok(()) };
    match Key::load(repo, &config) {
        Ok(Some(key)) if key.private() => {},
        // Locked, or unlocked without the private mode: nothing to do.
        Ok(_) => return Ok(()),
        // The finished Git command must not fail; say why nothing happened.
        Err(e) => {
            eprintln!("transcrypt-rs: automatic decryption skipped: {e}");
            return Ok(());
        },
    }
    match hydrate(repo) {
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
pub(crate) fn hydrate(repo: &Repository) -> Result<usize, String> {
    hydrate_locked(repo, &staging_dir(repo)?)
}

/// The protected paths among `paths`, by the staged attributes.
pub(crate) fn protected_paths(repo: &Repository, paths: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, String> {
    let refs: Vec<&[u8]> = paths.iter().map(Vec::as_slice).collect();
    let flags = protected_flags(repo, &refs, Attributes::Staged)?;
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
pub(crate) fn hydrate_locked(repo: &Repository, staging: &Staging) -> Result<usize, String> {
    let config = load_config(repo)?;
    let key = Key::require(repo, &config)?;
    let index = index_with_conflicts(repo)?;
    let conflicted = protected_paths(repo, &index.conflicted)?;
    let protected: Vec<Staged> = if conflicted.is_empty() {
        // Authenticate ALL staged protected objects and the staged config
        // before exposing any plaintext in the checkout.
        let snapshot = Snapshot::of(repo, Listing::parse(index.listing.clone())?)?;
        check_staged(repo, &config, snapshot, &commit_listing(repo, "HEAD")?, Some(&key), false)?.protected
    } else {
        // A merge is in progress: the stages of an unmerged path are the
        // merge's inputs, not a snapshot to verify. Plaintext published here
        // is encrypted again by `git add`, since the paths are protected.
        staged_protected(repo, index.merged)?
    };
    let id = transcrypt_rs::config_id(&config);
    let mut pending = Vec::new();
    let mut refresh = Vec::new();
    let mut kept = Vec::new();

    // Decide for every file before writing any. A protected symlink or
    // unreadable file aborts the whole operation. Unmerged files have no
    // staged record of their own; they are decrypted when they hold a
    // record that authenticates at their path (the merge driver's result).
    let targets = protected.iter().map(|e| (e.path.as_slice(), Some(&e.oid)))
        .chain(conflicted.iter().map(|p| (p.as_slice(), None)));
    for (path, oid) in targets {
        let relative = indexed_path(path)?;
        // A deleted (or sparse) file holds nothing to decrypt.
        let Some(target) = find_protected(repo.root(), &relative)? else { continue };
        let (worktree, stamp) = target.read()?;
        let object = oid.map(|oid| git_blob(repo, oid)).transpose()?;
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
    if index_listing(repo)? != index.listing || load_config(repo)? != config {
        return Err("index or public configuration changed during hydration".into());
    }
    let published = pending.len();
    for Publish { path, relative, stamp, plaintext, staged } in pending {
        // `replace` refuses unless the file is still the record checked above.
        open_protected(repo.root(), &relative)?.replace(staging, &plaintext, &stamp, key.private())?;
        if staged { refresh.push(path.to_vec()); }
    }
    // Private mode: plaintext that Git's checkout wrote follows the umask
    // and may be readable by other users.
    if key.private() {
        for relative in &kept {
            open_protected(repo.root(), relative)?.make_private()?;
        }
    }
    // Git's index still caches the size/mtime of the encrypted checkout, and
    // `update-index --refresh` skips files whose size changed. Re-index the
    // files that now hold exactly the staged plaintext (never an edit or a
    // different version, which would stage it) through the clean filter:
    // `update-index -z --stdin` takes raw path bytes, never pathspecs, and
    // without `--add` cannot stage an untracked file. `reindex` verifies that
    // no staged blob or mode changed, even when index != HEAD.
    reindex(repo, &index.listing, &refresh)?;
    Ok(published)
}

/// `lock`: replace the plaintext of every worktree of this repository by
/// its committed records, then forget the key (the stored file, or the
/// private agent). Any refusal keeps the key.
pub(crate) fn lock(repo: &Repository) -> Result<(), String> {
    let config = load_config(repo)?;
    let Some(key) = Key::load(repo, &config)? else {
        // No usable key here: nothing can be flushed. Locked means no
        // plaintext is left in any worktree; another worktree on another
        // config may still need the stored key to lock.
        worktree_encrypted(repo, &config)
            .map_err(|e| format!("{e}, but there is no key to encrypt it: unlock, then lock"))?;
        others_encrypted(repo)?;
        crate::credential::forget(repo)?;
        eprintln!("Already locked.");
        return Ok(());
    };
    for other in other_worktrees(repo)? {
        let flushed = run_in(&other, "flush")
            .map_err(|e| format!("cannot lock worktree {}: {e}", other.display()))?.status.success();
        // A worktree on another config cannot be flushed with this key; it
        // is fine if it holds no plaintext.
        if !flushed && !run_in(&other, "check-encrypted").is_ok_and(|f| f.status.success()) {
            return Err(format!("worktree {} could not be locked (uncommitted changes, or plaintext under \
                another config); the key is kept", other.display()));
        }
    }
    flush(repo)?;
    if key.private() {
        crate::session::stop(repo, &config)?;
    } else {
        crate::credential::forget(repo)?;
    }
    eprintln!("Locked: protected files replaced by their ciphertext and the key forgotten. \
        This does not securely erase earlier plaintext copies.");
    Ok(())
}

/// Refuse unless every other worktree holds no plaintext (each checked in
/// its own process, with its own config).
pub(crate) fn others_encrypted(repo: &Repository) -> Result<(), String> {
    for other in other_worktrees(repo)? {
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
fn other_worktrees(repo: &Repository) -> Result<Vec<PathBuf>, String> {
    let this = repo.root().canonicalize().map_err(|_| "cannot resolve the repository root")?;
    let mut others = Vec::new();
    for worktree in worktrees(repo)? {
        if worktree.bare || worktree.prunable { continue; }
        let path = worktree.path.canonicalize()
            .map_err(|e| format!("cannot inspect worktree {}: {e}", worktree.path.display()))?;
        if path != this { others.push(worktree.path); }
    }
    Ok(others)
}

/// Replace this worktree's plaintext by the committed records, keeping the
/// key (`lock` forgets it once every worktree is done).
pub(crate) fn flush(repo: &Repository) -> Result<(), String> {
    let staging = staging_dir(repo)?;
    let config = load_config(repo)?;
    let key = Key::require(repo, &config)?;
    // Every protected file must match the encrypted index BEFORE any
    // worktree rewrite. If anything is dirty or untracked, keep the key.
    let verified = check_index(repo, Some(&key))?;
    untracked_protected(repo)?;
    let mut to_flush = Vec::new();
    let mut present = Vec::new();
    for staged in &verified.protected {
        let relative = indexed_path(&staged.path)?;
        // A deleted file holds no plaintext: nothing to flush.
        let Some(target) = find_protected(repo.root(), &relative)? else { continue };
        present.push(staged.path.clone());
        let (source, stamp) = target.read()?;
        // The object the index named when it was verified, by object id.
        let object = git_blob(repo, &staged.oid)?;
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
        open_protected(repo.root(), relative)?.replace(&staging, object, stamp, false)?;
    }
    // Refresh Git's cached stat data for the ciphertext now in the worktree
    // (the clean filter returns an authentic record unchanged), so a locked
    // checkout is clean and `git commit -a` does not need the key.
    reindex(repo, &verified.listing, &present)?;
    Ok(())
}

/// Refuse if an untracked file is protected: its plaintext would be left
/// behind by `lock`. Ignored files count too (no `--exclude-standard`, unlike
/// `status`): an ignored protected file, such as a `.env`, holds plaintext all
/// the same.
fn untracked_protected(repo: &Repository) -> Result<(), String> {
    let untracked = git(repo, &["ls-files", "--others", "-z"])?;
    let paths = git_records(&untracked)?;
    let flags = protected_flags(repo, &paths, Attributes::Worktree)?;
    if let Some((path, _)) = paths.iter().zip(flags).find(|(_, p)| *p) {
        return Err(format!("untracked protected file {} holds plaintext; add or remove it first",
            String::from_utf8_lossy(path)));
    }
    Ok(())
}

/// Whether the worktree holds no plaintext secret: every protected tracked
/// file present has the v3 envelope of this config, and no untracked file
/// is protected.
pub(crate) fn worktree_encrypted(repo: &Repository, config: &[u8]) -> Result<(), String> {
    let id = transcrypt_rs::config_id(config);
    for staged in protected_entries(repo, indexed_files(repo)?, Attributes::Staged)? {
        if let Some(target) = find_protected(repo.root(), &indexed_path(&staged.path)?)? {
            let (contents, _) = target.read()?;
            if !record_envelope_ok(&contents, &id) {
                return Err(format!("{} holds plaintext", staged.name()));
            }
        }
    }
    untracked_protected(repo)
}
