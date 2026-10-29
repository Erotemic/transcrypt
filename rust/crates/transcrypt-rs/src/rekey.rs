//! Key rotation: `rekey` (a new passphrase and config, every staged record
//! re-encrypted) and `reencrypt` (records still under an earlier config
//! brought forward).

use transcrypt_rs::unlock_config;
use transcrypt_v3_core::parse_file_header;
use crate::{
    attributes::owned_paths,
    credential::Key,
    git::*,
    lifecycle::*,
    load_config, passphrase, session,
    setup::{activate, new_config},
    worktree::{find_protected, indexed_path, replace_if_holds, staging_dir, write_repository_file},
    Options,
};
use std::path::Path;

/// A config id.
type Id = [u8; transcrypt_v3_core::ID_LEN];

/// Change the passphrase. Every protected file must be committed (no edit
/// is mixed into the re-encryption). A fresh salt and key give a new config;
/// every staged record is re-encrypted under it, and all of them plus the
/// config are staged in one index update for the user to commit. Only then
/// does the worktree config, written like a protected file (never through a
/// symlink), and the credential switch to the new key. Commits made before
/// keep their old records, readable with the old passphrase.
pub(crate) fn rekey(root: &Path, options: &Options) -> Result<(), String> {
    let old_config = load_config(root)?;
    let old_key = Key::load(root, &old_config)?.ok_or("unlock with the current passphrase first")?;
    let password = passphrase(options.password_stdin, true)?;
    // No hydrate or lock may run meanwhile.
    let staging = staging_dir(root)?;
    // Decrypt everything first, then require that each file is exactly the
    // plaintext of its staged record.
    hydrate_locked(root, &staging)?;
    let verified = check_index(root, Some(&old_key))?;
    let mut plaintexts = Vec::new();
    for staged in &verified.protected {
        let plaintext = old_key.open(&staged.path, &git_blob(root, &staged.oid)?)?;
        let unchanged = find_protected(root, &indexed_path(&staged.path)?)?.map(|t| t.read()).transpose()?
            .is_some_and(|(worktree, _)| *worktree == *plaintext);
        if !unchanged {
            return Err(format!("{} has uncommitted changes (or was deleted); commit or discard them before \
                rekeying", staged.name()));
        }
        plaintexts.push((staged, plaintext));
    }
    let (config, key) = new_config(&password)?;
    // The new records, written as Git objects, and one index update.
    let mut update = IndexUpdate::default();
    for (staged, plaintext) in &plaintexts {
        update.add(&staged.mode, &staged.path, &transcrypt_rs::encrypt_file(&config, &key, &staged.path, plaintext)?);
    }
    update.add(REGULAR_FILE_MODE, CONFIG_PATH.as_bytes(), &config);
    update.apply(root, &[])?;
    let undo = "; run `git reset` to undo the staged rekey";
    write_repository_file(root, &staging, Path::new(CONFIG_PATH), &config)
        .map_err(|e| format!("{e}{undo}"))?;
    if old_key.private() {
        session::stop(root, &old_config)?;
    }
    activate(root, &config, &key, old_key.private(), None)
        .map_err(|e| format!("{e}; the rekey is staged: run `transcrypt-rs unlock` with the NEW passphrase"))?;
    drop(staging);
    // The worktree plaintext now cleans to the new staged records.
    reindex(root, &index_listing(root)?, &owned_paths(&verified.protected))?;
    eprintln!("Rekeyed {} file(s); the new config and records are staged. Commit them now, e.g.\n  \
        git commit -m 'Rekey transcrypt-v3'\n\
        Earlier commits stay readable with the old passphrase: if it was exposed, change the secrets themselves.",
        plaintexts.len());
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
pub(crate) fn reencrypt(root: &Path, options: &Options) -> Result<(), String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let stale = stale_files(root, &transcrypt_rs::config_id(&config))?;
    if stale.is_empty() {
        eprintln!("Every staged protected file is encrypted under the current config.");
        return Ok(());
    }
    let configs = earlier_configs(root, &config)?;
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
    let head = commit_files(root, "HEAD")?;
    for file in &stale {
        eprintln!("  {} (config {}; {})", file.staged.name(), crate::short_id(&file.config), origin(root, &head, &file.staged));
    }
    if !options.yes {
        let confirmed = !options.password_stdin && rpassword::prompt_password("Type yes to continue: ")
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
        let password = passphrase(options.password_stdin, false)?;
        keys.push((old, unlock_config(&password, &old.bytes)?));
    }
    let mut update = IndexUpdate::default();
    let staging = staging_dir(root)?;
    for (old, old_key) in &keys {
        for Stale { staged, record, .. } in stale.iter().filter(|f| f.config == old.id) {
            let plaintext = transcrypt_rs::decrypt_file(&old.bytes, old_key, &staged.path, record)
                .map_err(|e| format!("{}: {e}", staged.name()))?;
            update.add(&staged.mode, &staged.path, &key.clean(&staged.path, &plaintext)?);
            replace_if_holds(root, &staging, &staged.path, record, &plaintext, key.private())?;
        }
    }
    update.apply(root, &[])?;
    eprintln!("Re-encrypted {} file(s) under the current config; they are staged. Commit them.", stale.len());
    Ok(())
}

/// The staged protected files whose records name a config other than `id`.
fn stale_files(root: &Path, id: &Id) -> Result<Vec<Stale>, String> {
    let mut stale = Vec::new();
    for staged in staged_protected(root, indexed_files(root)?)? {
        let record = git_blob(root, &staged.oid)?;
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

fn earlier_configs(root: &Path, current: &[u8]) -> Result<Vec<Earlier>, String> {
    let mut configs: Vec<Earlier> = Vec::new();
    let log = git(root, &["log", "--format=%H %s", "HEAD", "--", CONFIG_PATH])?;
    for line in String::from_utf8_lossy(&log).lines() {
        let (commit, subject) = line.split_once(' ').unwrap_or((line, ""));
        if let Some(oid) = config_blob(root, commit)? {
            let bytes = git_blob(root, &oid)?;
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
fn origin(root: &Path, head: &[Staged], staged: &Staged) -> String {
    if head.iter().any(|e| e.path == staged.path && e.oid == staged.oid) {
        return git(root, &["log", "-1", "--format=%h by %an: %s", "HEAD", "--", &staged.name()])
            .map(|o| format!("committed in {}", String::from_utf8_lossy(&o).trim())).unwrap_or_default();
    }
    let pending: Vec<String> = ["MERGE_HEAD", "CHERRY_PICK_HEAD", "REBASE_HEAD", "REVERT_HEAD"].iter()
        .filter_map(|r| git(root, &["log", "-1", "--format=%h by %an: %s", r]).ok()
            .map(|o| format!("{r} {}", String::from_utf8_lossy(&o).trim())))
        .collect();
    if pending.is_empty() { "staged, not committed: origin unknown".to_owned() }
    else { format!("staged, not committed; in progress: {}", pending.join("; ")) }
}
