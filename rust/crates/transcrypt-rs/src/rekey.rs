//! Key rotation: `rekey` (a new passphrase and config, every staged record
//! re-encrypted) and `reencrypt` (records still under an earlier config
//! brought forward).

use transcrypt_rs::{Profile, ValidatedKey};
use transcrypt_v3_core::{config_recovery, entry_recovery, file_recovery, parse_file_header, ConfigRecovery, EntryRecovery, FileRecovery};
use crate::{
    attributes::owned_paths,
    credential::Key,
    git::*,
    lifecycle::*,
    load_config, passphrase, session,
    setup::{activate, new_config},
    worktree::{find_protected, indexed_path, replace_if_holds, staging_dir, write_repository_file},
    cli::{KeyMode, ReencryptArgs, Resume},
    journal::{JournalEntry, RekeyJournal, REKEY_PENDING},
};
use std::{collections::HashMap, path::Path};

/// A config id.
type Id = [u8; transcrypt_v3_core::ID_LEN];

/// Change the passphrase. Every protected file must be committed (no edit
/// is mixed into the re-encryption). A fresh salt and key give a new config;
/// every staged record is re-encrypted under it, and all of them plus the
/// config are staged in one index update for the user to commit. Only then
/// does the worktree config, written like a protected file (never through a
/// symlink), and the credential switch to the new key. Commits made before
/// keep their old records, readable with the old passphrase. The new one is
/// read from stdin with `password_stdin`.
///
/// Before the index changes, a journal (`journal.rs`) records each entry
/// it replaces, as it was and as it becomes; it is removed at the end. If
/// the rekey is interrupted, `rekey --continue` or `rekey --abort`
/// (`resume`) finishes or undoes exactly those entries.
pub(crate) fn rekey(repo: &Repository, password_stdin: bool, profile: Option<Profile>) -> Result<(), String> {
    if RekeyJournal::pending(repo) {
        return Err(REKEY_PENDING.into());
    }
    let old_config = load_config(repo)?;
    let old_key = Key::load(repo, &old_config)?.ok_or("unlock with the current passphrase first")?;
    // The current profile unless one is named: a conversion is explicit.
    let profile = match profile {
        Some(profile) => profile,
        None => transcrypt_rs::config_profile(&old_config)?,
    };
    let password = passphrase(password_stdin, true)?;
    // No hydrate or lock may run meanwhile.
    let staging = staging_dir(repo)?;
    // Decrypt everything first, then require that each file is exactly the
    // plaintext of its staged record.
    hydrate_locked(repo, &staging)?;
    let verified = check_index(repo, Some(&old_key))?;
    let mut plaintexts = Vec::new();
    for staged in &verified.protected {
        let plaintext = old_key.open(&staged.path, &git_blob(repo, &staged.oid)?)?;
        let unchanged = find_protected(repo.root(), &indexed_path(&staged.path)?)?.map(|t| t.read()).transpose()?
            .is_some_and(|(worktree, _)| *worktree == *plaintext);
        if !unchanged {
            return Err(format!("{} has uncommitted changes (or was deleted); commit or discard them before \
                rekeying", staged.name()));
        }
        plaintexts.push((staged, plaintext));
    }
    let staged_config = indexed_files(repo)?.into_iter().find(|e| e.path == CONFIG_PATH.as_bytes() && e.regular())
        .ok_or(".transcrypt/config is not staged; `git add .transcrypt/config` first")?;
    let old_config_id = hash_object(repo, &old_config)?;
    let key = new_config(profile, &password)?;
    let config = key.config();
    // The new records, written as Git objects; then the journal; then one
    // index update.
    let mut update = IndexUpdate::new(repo, Blobs::Records);
    for (staged, plaintext) in &plaintexts {
        update.add(staged.mode, &staged.path, &key.encrypt(&staged.path, plaintext)?)?;
    }
    update.add(Mode::REGULAR, CONFIG_PATH.as_bytes(), config)?;
    let written = update.write()?;
    let old_ids = plaintexts.iter().map(|(staged, _)| &staged.oid).chain([&staged_config.oid]);
    let entries: Vec<JournalEntry> = written.entries.iter().zip(old_ids)
        .map(|((mode, new, path), old)| JournalEntry { mode: *mode, old: old.clone(), new: new.clone(), path: path.clone() })
        .collect();
    let new_config_id = entries.last().map(|e| e.new.clone()).ok_or("internal error: no config entry")?;
    RekeyJournal { old_config: old_config_id, new_config: new_config_id, entries }.save(repo)?;
    written.apply(&[])?;
    write_repository_file(repo.root(), &staging, Path::new(CONFIG_PATH), config)
        .map_err(|e| format!("{e}; there is {REKEY_PENDING}"))?;
    if old_key.private() {
        session::stop(repo, &old_config)?;
    }
    let mode = if old_key.private() { KeyMode::Private { idle: None } } else { KeyMode::Stored };
    activate(repo, &key, mode).map_err(|e| format!("{e}; there is {REKEY_PENDING}"))?;
    drop(staging);
    // The worktree plaintext now cleans to the new staged records.
    reindex(repo, &index_listing(repo)?, &owned_paths(&verified.protected))
        .map_err(|e| format!("{e}; there is {REKEY_PENDING}"))?;
    RekeyJournal::remove(repo)?;
    eprintln!("Rekeyed {} file(s) under {}; the new config and records are staged. Commit them now, e.g.\n  \
        git commit -m 'Rekey transcrypt-v3'\n\
        Earlier commits stay readable with the old passphrase: if it was exposed, change the secrets themselves.",
        plaintexts.len(), transcrypt_rs::profile_description(profile));
    Ok(())
}

/// `rekey --continue` (`Resume::Continue`) or `rekey --abort`: bring each
/// entry of the journal to its new (continue) or old (abort) object, with
/// the worktree config and the key to match. Lossless: if an entry, or the
/// worktree config, is neither what the rekey found nor what it wrote, it
/// changed afterwards, and nothing is changed; no other entry is touched. A
/// worktree file holding the record being replaced (a locked checkout) gets
/// the other record; one holding the plaintext stays and is re-indexed; one
/// holding anything else (an edit) is left as it is. Rerunning after an
/// interruption finishes the job. The passphrase (from stdin with
/// `password_stdin`) is asked only if no key for the resulting config is
/// already in use.
pub(crate) fn resume(repo: &Repository, password_stdin: bool, resume: Resume) -> Result<(), String> {
    let journal = RekeyJournal::load(repo)?.ok_or("no interrupted rekey here (nothing to continue or abort)")?;
    let forward = resume == Resume::Continue;
    let (flag, which) = if forward { ("--continue", "new") } else { ("--abort", "old") };
    let ends = |e: &JournalEntry| if forward { (e.new.clone(), e.old.clone()) } else { (e.old.clone(), e.new.clone()) };
    let (want_config_id, from_config_id) = if forward { (&journal.new_config, &journal.old_config) }
        else { (&journal.old_config, &journal.new_config) };
    let ids: Vec<&ObjectId> = [&journal.old_config, &journal.new_config].into_iter()
        .chain(journal.entries.iter().flat_map(|e| [&e.old, &e.new])).collect();
    let mut query = Vec::new();
    for id in &ids { query.extend_from_slice(format!("{id}\n").as_bytes()); }
    let types = git_with_input(repo, &["cat-file", "--batch-check=%(objecttype)"], &query)?;
    if String::from_utf8_lossy(&types).lines().count() != ids.len() || String::from_utf8_lossy(&types).lines().any(|t| t != "blob") {
        return Err("the rekey journal names objects this repository lacks".into());
    }
    let want_config = git_blob(repo, want_config_id)?;
    let from_config = git_blob(repo, from_config_id)?;
    transcrypt_rs::config_profile(&want_config)?;
    // No hydrate or lock may run meanwhile.
    let staging = staging_dir(repo)?;
    let index = index_with_conflicts(repo)?;
    let now: HashMap<&[u8], (Mode, &ObjectId)> = index.merged.iter().map(|e| (&e.path[..], (e.mode, &e.oid))).collect();
    let mut todo = Vec::new();
    let mut changed = Vec::new();
    for entry in &journal.entries {
        let (want, from) = ends(entry);
        let staged = now.get(&entry.path[..]).filter(|(mode, _)| *mode == entry.mode);
        let oid = staged.map_or(&[][..], |(_, oid)| oid.as_str().as_bytes());
        match entry_recovery(staged.is_some(), oid, want.as_str().as_bytes(), from.as_str().as_bytes()) {
            EntryRecovery::Done => {},
            EntryRecovery::Todo => todo.push((entry.mode, want, entry.path.clone())),
            EntryRecovery::Changed => changed.push(format!("{} (staged)", String::from_utf8_lossy(&entry.path))),
        }
    }
    let worktree_config = find_protected(repo.root(), Path::new(CONFIG_PATH))
        .map_err(|_| "unsafe .transcrypt/config (a symlink or not a regular file)".to_owned())?
        .map(|file| file.read().map(|(bytes, _)| bytes.to_vec())).transpose()?;
    let config_state = config_recovery(worktree_config.is_some(), worktree_config.as_deref().unwrap_or_default(),
        &want_config, &from_config);
    if config_state == ConfigRecovery::Changed {
        changed.push(".transcrypt/config (worktree)".into());
    }
    if !changed.is_empty() {
        return Err(format!("changed since the rekey was interrupted, so {flag} would lose that change (nothing was \
            changed): {}; put back what the rekey left there (`git status`, `git diff --cached`), then rerun",
            changed.join(", ")));
    }
    // The key of the config this ends with: the one in use, or derived from
    // its passphrase (checked before anything is written).
    let current = Key::load(repo, &want_config)?;
    let derived = match current {
        Some(_) => None,
        None => {
            let password = passphrase(password_stdin, false)?;
            Some(ValidatedKey::unlock(&password, &want_config)
                .map_err(|e| format!("{e}: rekey {flag} needs the passphrase of the {which} config"))?)
        },
    };
    let open = |path: &[u8], record: &[u8]| match (&current, &derived) {
        (Some(key), _) => key.open(path, record),
        (None, Some(key)) => key.decrypt(path, record),
        (None, None) => Err("internal error: no key".into()),
    };
    // Each protected worktree file: the record being replaced (locked) gets
    // the other one; the plaintext stays and is re-indexed.
    let mut relock = Vec::new();
    let mut reindexed = Vec::new();
    for entry in journal.entries.iter().filter(|e| e.path != CONFIG_PATH.as_bytes()) {
        let Some(target) = find_protected(repo.root(), &indexed_path(&entry.path)?)? else { continue };
        let (worktree, _) = target.read()?;
        let (want, from) = ends(entry);
        let (want_record, from_record) = (git_blob(repo, &want)?, git_blob(repo, &from)?);
        match file_recovery(&worktree, &want_record, &from_record) {
            FileRecovery::Relock => relock.push((entry.path.clone(), from_record, want_record)),
            FileRecovery::Keep => {},
            // Never written; re-indexed if it is the plaintext of the record.
            FileRecovery::Check => if open(&entry.path, &want_record).is_ok_and(|p| *p == *worktree) {
                reindexed.push(entry.path.clone());
            },
        }
    }
    let private = Key::load(repo, &from_config)?.is_some_and(|k| k.private());
    if let Some(key) = &derived {
        if private { session::stop(repo, &from_config)?; }
        activate(repo, key, if private { KeyMode::Private { idle: None } } else { KeyMode::Stored })?;
    }
    if config_state == ConfigRecovery::Write {
        write_repository_file(repo.root(), &staging, Path::new(CONFIG_PATH), &want_config)?;
    }
    stage_objects(repo, &todo, &[])?;
    for (path, from_record, want_record) in &relock {
        replace_if_holds(repo.root(), &staging, path, from_record, want_record, false)?;
        reindexed.push(path.clone());
    }
    drop(staging);
    reindexed.push(CONFIG_PATH.as_bytes().to_vec());
    reindex(repo, &index_listing(repo)?, &reindexed)?;
    RekeyJournal::remove(repo)?;
    if forward {
        eprintln!("Finished the interrupted rekey: {} entries staged under the new config; commit them.", journal.entries.len());
    } else {
        eprintln!("Undid the interrupted rekey: {} staged entries put back, the old config and key restored; nothing \
            else was changed.", todo.len());
    }
    Ok(())
}

/// A staged protected file still encrypted under an earlier config.
struct Stale {
    staged: Staged,
    record: Vec<u8>,
    /// The id of the config its record names.
    config: Id,
}

/// A config from this branch's history before the current one.
struct Earlier {
    bytes: Vec<u8>,
    id: Id,
    /// The commit that introduced it: abbreviated id and subject.
    introduced: String,
}

/// `reencrypt`: staged protected files still encrypted under an earlier
/// config (a commit cherry-picked or rebased across a `rekey` brings its
/// records unchanged) are opened under that config, found in history and
/// authenticated with its passphrase, at their own path, and re-sealed under
/// the current config. Nothing else changes; the result is staged.
pub(crate) fn reencrypt(repo: &Repository, args: &ReencryptArgs) -> Result<(), String> {
    let config = load_config(repo)?;
    let key = Key::require(repo, &config)?;
    let stale = stale_files(repo, &transcrypt_rs::config_id(&config))?;
    if stale.is_empty() {
        eprintln!("Every staged protected file is encrypted under the current config.");
        return Ok(());
    }
    let configs = earlier_configs(repo, &config)?;
    if let Some(file) = stale.iter().find(|f| !configs.iter().any(|c| c.id == f.config)) {
        return Err(format!("{} is encrypted under a config this branch never had before its current one \
            (from another branch, or newer); `reencrypt` only brings forward earlier configs of this branch",
            file.staged.name()));
    }
    // An explicit trust decision: whoever holds an earlier passphrase can
    // forge records under it, and re-sealing makes them genuine under the
    // current config. Show where each one came from.
    eprintln!("These staged files are encrypted under an earlier config. Re-encrypting them makes their \
        content trusted under the current config:");
    let head = commit_files(repo, "HEAD")?;
    for file in &stale {
        eprintln!("  {} (config {}; {})", file.staged.name(), crate::short_id(&file.config), origin(repo, &head, &file.staged));
    }
    if !args.yes {
        let confirmed = !args.password_stdin && rpassword::prompt_password("Type yes to continue: ")
            .is_ok_and(|answer| answer.trim() == "yes");
        if !confirmed {
            return Err("not confirmed; review those commits, then run `transcrypt-rs reencrypt --yes`".into());
        }
    }
    // Every earlier passphrase is asked for and checked before any write.
    let mut keys = Vec::new();
    for old in configs.iter().filter(|c| stale.iter().any(|f| f.config == c.id)) {
        let names: Vec<String> = stale.iter().filter(|f| f.config == old.id).map(|f| f.staged.name().into_owned()).collect();
        eprintln!("Passphrase of config {} (introduced by {}), for: {}",
            crate::short_id(&old.id), old.introduced, names.join(", "));
        let password = passphrase(args.password_stdin, false)?;
        keys.push((old, ValidatedKey::unlock(&password, &old.bytes)?));
    }
    // Decrypt and re-seal every file before writing any.
    let mut resealed = Vec::new();
    for (old, old_key) in &keys {
        for Stale { staged, record, .. } in stale.iter().filter(|f| f.config == old.id) {
            let plaintext = old_key.decrypt(&staged.path, record)
                .map_err(|e| format!("{}: {e}", staged.name()))?;
            let new_record = key.clean(&staged.path, &plaintext)?;
            resealed.push((staged, record, plaintext, new_record));
        }
    }
    // The worktree first: a file that still holds its old record gets the
    // plaintext. The index changes last, so after a failure it still names
    // the old records and rerunning `reencrypt` finishes the job.
    let staging = staging_dir(repo)?;
    for (staged, record, plaintext, _) in &resealed {
        replace_if_holds(repo.root(), &staging, &staged.path, record, plaintext, key.private())?;
    }
    let mut update = IndexUpdate::new(repo, Blobs::Records);
    for (staged, _, _, new_record) in &resealed {
        update.add(staged.mode, &staged.path, new_record)?;
    }
    update.apply(&[])?;
    eprintln!("Re-encrypted {} file(s) under the current config; they are staged. Commit them.", stale.len());
    Ok(())
}

/// The staged protected files whose records name a config other than `id`.
fn stale_files(repo: &Repository, id: &Id) -> Result<Vec<Stale>, String> {
    let mut stale = Vec::new();
    for staged in staged_protected(repo, indexed_files(repo)?)? {
        let record = git_blob(repo, &staged.oid)?;
        if let Ok(found) = parse_file_header(&record) {
            if found != *id { stale.push(Stale { staged, record, config: found }); }
        }
    }
    Ok(stale)
}

/// Configs from this branch's history other than the current one: a
/// safety net against adopting another branch's config or newer content,
/// not a guarantee (history is a graph; a reverted rekey reappears).
/// Hex digits of a commit id shown to identify it to people.
const SHORT_COMMIT_LEN: usize = 12;

fn earlier_configs(repo: &Repository, current: &[u8]) -> Result<Vec<Earlier>, String> {
    let mut configs: Vec<Earlier> = Vec::new();
    let log = git(repo, &["log", "--format=%H %s", "HEAD", "--", CONFIG_PATH])?;
    for line in String::from_utf8_lossy(&log).lines() {
        let (commit, subject) = line.split_once(' ').unwrap_or((line, ""));
        if let Some(oid) = config_blob(repo, commit)? {
            let bytes = git_blob(repo, &oid)?;
            if bytes != current && transcrypt_v3_core::parse_config(&bytes).is_ok()
                && !configs.iter().any(|c| c.bytes == bytes) {
                let id = transcrypt_rs::config_id(&bytes);
                configs.push(Earlier { bytes, id, introduced: format!("{} {subject}", &commit[..commit.len().min(SHORT_COMMIT_LEN)]) });
            }
        }
    }
    Ok(configs)
}

/// Where the staged blob came from: `HEAD`'s last change to the path only
/// if `HEAD` (whose files are `head`) has this very blob there; otherwise
/// it is staged.
fn origin(repo: &Repository, head: &[Staged], staged: &Staged) -> String {
    if head.iter().any(|e| e.path == staged.path && e.oid == staged.oid) {
        return git(repo, &["log", "-1", "--format=%h by %an: %s", "HEAD", "--", &staged.name()])
            .map(|o| format!("committed in {}", String::from_utf8_lossy(&o).trim())).unwrap_or_default();
    }
    let pending: Vec<String> = ["MERGE_HEAD", "CHERRY_PICK_HEAD", "REBASE_HEAD", "REVERT_HEAD"].iter()
        .filter_map(|r| git(repo, &["log", "-1", "--format=%h by %an: %s", r]).ok()
            .map(|o| format!("{r} {}", String::from_utf8_lossy(&o).trim())))
        .collect();
    if pending.is_empty() { "staged, not committed: origin unknown".to_owned() }
    else { format!("staged, not committed; in progress: {}", pending.join("; ")) }
}
