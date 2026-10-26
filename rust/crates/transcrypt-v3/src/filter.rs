//! The clean and smudge filters: per file (`clean`/`smudge %f`) or for a
//! whole Git command (`filter-process`, in `process.rs`).

use std::{fs, path::Path};
use zeroize::Zeroizing;
use transcrypt_v3_core::{parse_file_header, record_envelope_ok, smudge_action, Refusal, SmudgeAction};
use crate::{credential::Key, git::*, load_config, worktree::{find_protected, indexed_path}};

/// The clean and smudge filters of one Git process (one file, or every file
/// of a Git command for `filter-process`). The worktree config is re-read
/// for every file (a checkout or rebase can change it mid-command) and the
/// key reloaded when it changes.
pub(crate) struct Filters<'a> {
    root: &'a Path,
    current: Option<(Vec<u8>, Option<Key>)>,
    stored: Option<Option<Key>>,
    /// The staged config, when a sparse checkout leaves `.transcrypt/` out
    /// of the worktree (the index does not change within a Git command).
    staged_config: Option<Vec<u8>>,
}

impl<'a> Filters<'a> {
    pub(crate) fn new(root: &'a Path) -> Filters<'a> {
        Filters { root, current: None, stored: None, staged_config: None }
    }

    /// One clean or smudge conversion of the file at `git_path`.
    pub(crate) fn convert(&mut self, clean: bool, git_path: &[u8], input: Zeroizing<Vec<u8>>)
        -> Result<Zeroizing<Vec<u8>>, String>
    {
        if transcrypt_v3_core::is_reserved_path(git_path) {
            return Err(format!("{} is selected for encryption, but v3 never encrypts .gitattributes, \
                .gitmodules or .transcrypt/; narrow the .gitattributes pattern that selects it",
                String::from_utf8_lossy(git_path)));
        }
        transcrypt_v3::validate_protected_path(git_path)?;
        let config = if fs::symlink_metadata(self.root.join(".transcrypt")).is_ok() {
            load_config(self.root)?
        } else {
            if self.staged_config.is_none() { self.staged_config = Some(load_config(self.root)?); }
            self.staged_config.clone().unwrap_or_default()
        };
        if self.current.as_ref().map(|(c, _)| c) != Some(&config) {
            let key = Key::load(self.root, &config)?;
            self.current = Some((config, key));
        }
        let Filters { root, current: Some((config, current_key)), stored, .. } = self else { unreachable!() };
        let (root, key) = (*root, current_key.as_ref());
        let id = transcrypt_v3::config_id(config);
        let found = parse_file_header(&input).ok();
        if clean {
            // A record of another config (from before a rekey) cannot be
            // re-encrypted here. It passes through unchanged, so Git keeps
            // working, only if Git already has exactly these bytes at this
            // path (verification then refuses to commit it); anything else
            // starting with such a header is refused.
            if found.is_some_and(|found| found != id) {
                if blobs_at(root, git_path)?.contains(&blob_id(root, &input)?) { return Ok(input); }
                return Err(format!("{} starts like a record of another config but is not the one Git has \
                    for it; refusing to store it", String::from_utf8_lossy(git_path)));
            }
            let Some(key) = key else {
                // A worktree on another config than the stored key's (a branch
                // from before a rekey) shows files the stored key decrypted:
                // the record Git has for the path, if it opens to exactly
                // these bytes, is their clean form.
                // (Only plaintext needs this; a record goes on below.)
                if let Some(stored) = if found.is_none() { stored_key(stored, root)? } else { None } {
                    for oid in blobs_at(root, git_path)? {
                        let record = git_blob(root, &oid)?;
                        if parse_file_header(&record).is_ok_and(|f| f == stored.config_id())
                            && stored.open(git_path, &record).is_ok_and(|pt| *pt == *input) {
                            return Ok(Zeroizing::new(record));
                        }
                    }
                }
                // Locked: without the key nothing can be encrypted, but Git
                // re-cleans worktree files (a locked checkout holds
                // ciphertext), so a record of this configuration passes
                // through unchanged. Plaintext is refused, never stored.
                if record_envelope_ok(&input, &id) { return Ok(input); }
                return Err(Key::require(root, config).err().unwrap_or_default());
            };
            // `clean` returns a record that already opens at this path
            // unchanged and otherwise seals with the verified core's
            // `seal_record`, which refuses any other v3 record.
            let record = key.clean(git_path, &input)?;
            if key.private() && *record != *input {
                // Private mode: Git is staging plaintext of this file; if it
                // was created readable by others, make it private now.
                if let Some(target) = indexed_path(git_path).and_then(|p| find_protected(root, &p))? {
                    target.make_private()?;
                }
            }
            return Ok(record);
        }
        // The key for the config the record names: the worktree's, or the
        // stored key's own (Git may smudge files of a checkout before it
        // writes the new `.transcrypt/config`).
        let key = match found {
            Some(found) if found == id => key,
            Some(found) => stored_key(stored, root)?.filter(|k| k.config_id() == found),
            None => None,
        };
        let decided = key.map_or(id, Key::config_id);
        // The verified core decides: bytes that are no v3 record are refused,
        // a record without a key here stays encrypted, and a record of the
        // key's config is opened, which authenticates it at this exact path
        // or fails.
        match smudge_action(&input, &decided, key.is_some()) {
            Ok(SmudgeAction::Keep) => {
                if found.is_some_and(|found| found != id) && current_key.is_some() {
                    eprintln!("transcrypt-v3: {} is encrypted under another config, without a key here; \
                        it stays encrypted (`transcrypt-v3 status` tells whether it needs `reencrypt`)",
                        String::from_utf8_lossy(git_path));
                }
                Ok(input)
            },
            Ok(SmudgeAction::Open) => {
                let Some(key) = key else { unreachable!() };
                let plaintext = key.open(git_path, &input).map_err(|_| {
                    let name = String::from_utf8_lossy(git_path);
                    format!("this record does not open at {name}: it was moved from another path or altered. \
                        If you moved it yourself (`git mv`), run `git add --renormalize -- {name}` or commit, which re-encrypts \
                        it; if it came from a commit, that commit is broken or hostile")
                })?;
                if key.private() && !umask_is_private() {
                    // Git would create this file readable by other users:
                    // keep the (now authenticated) record; the post-checkout
                    // hook or `hydrate` publishes the plaintext with mode 0600.
                    return Ok(input);
                }
                Ok(plaintext)
            },
            Err(Refusal::Foreign) => Err("the committed file is not v3 ciphertext (it was stored without the \
                filter); refusing to present it as a protected file".into()),
            Err(_) => Err(TOO_LARGE.into()),
        }
    }
}

/// The stored key, read at most once per process.
fn stored_key<'k>(slot: &'k mut Option<Option<Key>>, root: &Path) -> Result<Option<&'k Key>, String> {
    if slot.is_none() { *slot = Some(Key::stored(root)?); }
    Ok(slot.as_ref().and_then(Option::as_ref))
}

/// Whether files Git creates now are private to this user. Git creates
/// worktree files with mode `0666 & !umask`, and its filters inherit its
/// umask, so the smudge filter sees exactly the mask Git will apply.
pub(crate) fn umask_is_private() -> bool {
    // SAFETY: umask cannot fail; this process is single-threaded here and
    // restores the previous mask immediately.
    let previous = unsafe { libc::umask(0o077) };
    unsafe { libc::umask(previous) };
    previous & 0o077 == 0o077
}

