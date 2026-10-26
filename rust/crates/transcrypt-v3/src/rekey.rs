//! Key rotation: `rekey` (a new passphrase and config, every staged record
//! re-encrypted) and `reencrypt` (records still under an earlier config
//! brought forward).

use transcrypt_v3::unlock_config;
use transcrypt_v3_core::parse_file_header;
use crate::{
    credential::Key,
    git::*,
    lifecycle::*,
    load_config, passphrase, session,
    setup::{activate, new_config},
    worktree::{find_protected, indexed_path, replace_if_holds, staging_dir, write_repository_file},
    Options,
};
use std::path::Path;

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
    let mut index_info = Vec::new();
    for (staged, plaintext) in &plaintexts {
        let record = transcrypt_v3::encrypt_file(&config, &key, &staged.path, plaintext)?;
        push_blob_record(root, &mut index_info, &staged.mode, &staged.path, &record)?;
    }
    push_blob_record(root, &mut index_info, "100644", b".transcrypt/config", &config)?;
    git_with_input(root, &["update-index", "-z", "--index-info"], &index_info)?;
    let undo = "; run `git reset` to undo the staged rekey";
    write_repository_file(root, &staging, Path::new(".transcrypt/config"), &config)
        .map_err(|e| format!("{e}{undo}"))?;
    if old_key.private() {
        session::stop(root, &old_config)?;
    }
    activate(root, &config, &key, old_key.private(), None)
        .map_err(|e| format!("{e}; the rekey is staged: run `transcrypt-v3 unlock` with the NEW passphrase"))?;
    drop(staging);
    // The worktree plaintext now cleans to the new staged records.
    let paths: Vec<Vec<u8>> = verified.protected.iter().map(|e| e.path.clone()).collect();
    reindex(root, &index_listing(root)?, &paths)?;
    eprintln!("Rekeyed {} file(s); the new config and records are staged. Commit them now, e.g.\n  \
        git commit -m 'Rekey transcrypt-v3'\n\
        Earlier commits stay readable with the old passphrase: if it was exposed, change the secrets themselves.",
        plaintexts.len());
    Ok(())
}

/// `reencrypt`: staged protected files still encrypted under an earlier
/// config (a commit cherry-picked or rebased across a `rekey` brings its
/// records unchanged) are opened under that config, found in history and
/// authenticated with its passphrase, at their own path, and re-sealed under
/// the current config. Nothing else changes; the result is staged.
pub(crate) fn reencrypt(root: &Path, options: &Options) -> Result<(), String> {
    let config = load_config(root)?;
    let key = Key::require(root, &config)?;
    let id = transcrypt_v3::config_id(&config);
    let mut stale: Vec<(Staged, Vec<u8>, [u8; transcrypt_v3_core::ID_LEN])> = Vec::new();
    for staged in staged_protected(root, indexed_files(root)?)? {
        let record = git_blob(root, &staged.oid)?;
        if let Ok(found) = parse_file_header(&record) {
            if found != id { stale.push((staged, record, found)); }
        }
    }
    if stale.is_empty() {
        eprintln!("Every staged protected file is encrypted under the current config.");
        return Ok(());
    }
    // Configs from this branch's history other than the current one: a
    // safety net against adopting another branch's config or newer content,
    // not a guarantee (history is a graph; a reverted rekey reappears).
    type Id = [u8; transcrypt_v3_core::ID_LEN];
    let mut configs: Vec<(Vec<u8>, Id, String)> = Vec::new();
    let log = git(root, &["log", "--format=%H %s", "HEAD", "--", ".transcrypt/config"])?;
    for line in String::from_utf8_lossy(&log).lines() {
        let (commit, subject) = line.split_once(' ').unwrap_or((line, ""));
        if let Some(oid) = config_blob(root, commit)? {
            let bytes = git_blob(root, &oid)?;
            if bytes != config && transcrypt_v3_core::parse_config(&bytes).is_ok()
                && !configs.iter().any(|(c, _, _)| *c == bytes) {
                let id = transcrypt_v3::config_id(&bytes);
                configs.push((bytes, id, format!("{} {subject}", &commit[..commit.len().min(12)])));
            }
        }
    }
    if let Some((staged, _, _)) = stale.iter().find(|(_, _, f)| !configs.iter().any(|(_, id, _)| id == f)) {
        return Err(format!("{} is encrypted under a config this branch never had before its current one \
            (from another branch, or newer); `reencrypt` only brings forward earlier configs of this branch",
            staged.name()));
    }
    // An explicit trust decision: whoever holds an earlier passphrase can
    // forge records under it, and re-sealing makes them genuine under the
    // current config. Show where each one came from.
    eprintln!("These staged files are encrypted under an earlier config. Re-encrypting them makes their \
        content trusted under the current config:");
    let head = commit_files(root, "HEAD")?;
    for (staged, _, found) in &stale {
        let name = staged.name().into_owned();
        // Where the staged blob came from: `HEAD`'s last change to the path
        // only if `HEAD` has this very blob there; otherwise it is staged.
        let in_head = head.iter().any(|e| e.path == staged.path && e.oid == staged.oid);
        let origin = if in_head {
            git(root, &["log", "-1", "--format=%h by %an: %s", "HEAD", "--", &name])
                .map(|o| format!("committed in {}", String::from_utf8_lossy(&o).trim())).unwrap_or_default()
        } else {
            let pending: Vec<String> = ["MERGE_HEAD", "CHERRY_PICK_HEAD", "REBASE_HEAD", "REVERT_HEAD"].iter()
                .filter_map(|r| git(root, &["log", "-1", "--format=%h by %an: %s", r]).ok()
                    .map(|o| format!("{r} {}", String::from_utf8_lossy(&o).trim())))
                .collect();
            if pending.is_empty() { "staged, not committed: origin unknown".to_owned() }
            else { format!("staged, not committed; in progress: {}", pending.join("; ")) }
        };
        eprintln!("  {name} (config {}; {origin})", crate::hex(&found[..4]));
    }
    if !options.yes {
        let confirmed = !options.password_stdin && rpassword::prompt_password("Type yes to continue: ")
            .is_ok_and(|answer| answer.trim() == "yes");
        if !confirmed {
            return Err("not confirmed; review those commits, then run `transcrypt-v3 reencrypt --yes`".into());
        }
    }
    // Every earlier passphrase is asked for and checked before any write.
    let mut keys = Vec::new();
    for (old, old_id, introduced) in configs.iter().filter(|(_, id, _)| stale.iter().any(|(_, _, f)| f == id)) {
        let names: Vec<String> = stale.iter().filter(|(_, _, f)| f == old_id)
            .map(|(s, _, _)| s.name().into_owned()).collect();
        eprintln!("Passphrase of config {} (introduced by {introduced}), for: {}",
            crate::hex(&old_id[..4]), names.join(", "));
        let password = passphrase(options.password_stdin, false)?;
        keys.push((old, *old_id, unlock_config(&password, old)?));
    }
    let mut index_info = Vec::new();
    let staging = staging_dir(root)?;
    for (old, old_id, old_key) in &keys {
        for (staged, record, _) in stale.iter().filter(|(_, _, f)| f == old_id) {
            let plaintext = transcrypt_v3::decrypt_file(old, old_key, &staged.path, record)
                .map_err(|e| format!("{}: {e}", staged.name()))?;
            push_blob_record(root, &mut index_info, &staged.mode, &staged.path, &key.clean(&staged.path, &plaintext)?)?;
            replace_if_holds(root, &staging, &staged.path, record, &plaintext, key.private())?;
        }
    }
    git_with_input(root, &["update-index", "-z", "--index-info"], &index_info)?;
    eprintln!("Re-encrypted {} file(s) under the current config; they are staged. Commit them.", stale.len());
    Ok(())
}

