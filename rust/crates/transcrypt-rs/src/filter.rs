//! The clean and smudge filters: per file (`clean`/`smudge %f`) or for a
//! whole Git command (`filter-process`, in `process.rs`).

use std::{fs, path::Path};
use zeroize::Zeroizing;
use transcrypt_v3_core::{parse_file_header, record_envelope_ok, smudge_action, Refusal, SmudgeAction, ID_LEN};
use crate::{credential::Key, git::*, load_config, worktree::{find_protected, indexed_path}};

/// The clean and smudge filters of one Git process (one file, or every file
/// of a Git command for `filter-process`). The worktree config is re-read
/// for every file (a checkout or rebase can change it mid-command) and the
/// key reloaded when it changes.
pub(crate) struct Filters<'a> {
    root: &'a Path,
    current: Option<(Vec<u8>, Option<Key>)>,
    stored: StoredKey,
    /// The staged config, when a sparse checkout leaves `.transcrypt/` out
    /// of the worktree (the index does not change within a Git command).
    staged_config: Option<Vec<u8>>,
}

impl<'a> Filters<'a> {
    pub(crate) fn new(root: &'a Path) -> Filters<'a> {
        Filters { root, current: None, stored: StoredKey::NotRead, staged_config: None }
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
        transcrypt_rs::validate_protected_path(git_path)?;
        let config = self.config()?;
        let (config, key) = match &mut self.current {
            Some((current, key)) if *current == config => (&*current, &*key),
            slot => {
                let key = Key::load(self.root, &config)?;
                let (config, key) = slot.insert((config, key));
                (&*config, &*key)
            },
        };
        let file = File {
            root: self.root, path: git_path, config, key: key.as_ref(),
            id: transcrypt_rs::config_id(config), found: parse_file_header(&input).ok(),
        };
        if clean { file.clean(&mut self.stored, input) } else { file.smudge(&mut self.stored, input) }
    }

    /// The worktree config, or the staged one when the worktree has none.
    fn config(&mut self) -> Result<Vec<u8>, String> {
        if fs::symlink_metadata(self.root.join(".transcrypt")).is_ok() { return load_config(self.root); }
        if self.staged_config.is_none() { self.staged_config = Some(load_config(self.root)?); }
        Ok(self.staged_config.clone().unwrap_or_default())
    }
}

/// One file to convert under the current config `config` (whose id is
/// `id`) and its key, if any; `found` is the config id its header names.
struct File<'a> {
    root: &'a Path,
    path: &'a [u8],
    config: &'a [u8],
    key: Option<&'a Key>,
    id: [u8; ID_LEN],
    found: Option<[u8; ID_LEN]>,
}

impl File<'_> {
    fn clean(&self, stored: &mut StoredKey, input: Zeroizing<Vec<u8>>) -> Result<Zeroizing<Vec<u8>>, String> {
        let (root, git_path) = (self.root, self.path);
        // A record of another config (from before a rekey) cannot be
        // re-encrypted here. It passes through unchanged, so Git keeps
        // working, only if Git already has exactly these bytes at this
        // path (verification then refuses to commit it); anything else
        // starting with such a header is refused.
        if self.found.is_some_and(|found| found != self.id) {
            if blobs_at(root, git_path)?.contains(&blob_id(root, &input)?) { return Ok(input); }
            return Err(format!("{} starts like a record of another config but is not the one Git has \
                for it; refusing to store it", String::from_utf8_lossy(git_path)));
        }
        let Some(key) = self.key else { return self.clean_without_key(stored, input) };
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
        Ok(record)
    }

    fn clean_without_key(&self, stored: &mut StoredKey, input: Zeroizing<Vec<u8>>)
        -> Result<Zeroizing<Vec<u8>>, String>
    {
        let (root, git_path) = (self.root, self.path);
        // A worktree on another config than the stored key's (a branch
        // from before a rekey) shows files the stored key decrypted:
        // the record Git has for the path, if it opens to exactly
        // these bytes, is their clean form.
        // (Only plaintext needs this; a record goes on below.)
        if self.found.is_none() {
            if let Some(stored) = stored.get(root)? {
                for oid in blobs_at(root, git_path)? {
                    let record = git_blob(root, &oid)?;
                    if parse_file_header(&record).is_ok_and(|f| f == stored.config_id())
                        && stored.open(git_path, &record).is_ok_and(|pt| *pt == *input) {
                        return Ok(Zeroizing::new(record));
                    }
                }
            }
        }
        // Locked: without the key nothing can be encrypted, but Git
        // re-cleans worktree files (a locked checkout holds
        // ciphertext), so a record of this configuration passes
        // through unchanged. Plaintext is refused, never stored.
        if record_envelope_ok(&input, &self.id) { return Ok(input); }
        Err(Key::require(root, self.config).err().unwrap_or_default())
    }

    fn smudge(&self, stored: &mut StoredKey, input: Zeroizing<Vec<u8>>) -> Result<Zeroizing<Vec<u8>>, String> {
        let git_path = self.path;
        // The key for the config the record names: the worktree's, or the
        // stored key's own (Git may smudge files of a checkout before it
        // writes the new `.transcrypt/config`).
        let key = match self.found {
            Some(found) if found == self.id => self.key,
            Some(found) => stored.get(self.root)?.filter(|k| k.config_id() == found),
            None => None,
        };
        let decided = key.map_or(self.id, Key::config_id);
        // The verified core decides: bytes that are no v3 record are refused,
        // a record without a key here stays encrypted, and a record of the
        // key's config is opened, which authenticates it at this exact path
        // or fails. (It answers `Open` only when given a key.)
        match (smudge_action(&input, &decided, key.is_some()), key) {
            (Ok(SmudgeAction::Open), Some(key)) => {
                let plaintext = key.open(git_path, &input).map_err(|_| {
                    let name = String::from_utf8_lossy(git_path);
                    format!("this record does not open at {name}: it was moved from another path or altered. \
                        If you moved it yourself (`git mv`), run `git add --renormalize -- {name}` or commit, which re-encrypts \
                        it; if it came from a commit, that commit is broken or hostile")
                })?;
                if key.private() && !crate::os::checkouts_private() {
                    // Git would create this file readable by other users:
                    // keep the (now authenticated) record; the post-checkout
                    // hook or `hydrate` publishes the plaintext with mode 0600.
                    return Ok(input);
                }
                Ok(plaintext)
            },
            (Ok(_), _) => {
                if self.found.is_some_and(|found| found != self.id) && self.key.is_some() {
                    eprintln!("transcrypt-rs: {} is encrypted under another config, without a key here; \
                        it stays encrypted (`transcrypt-rs status` tells whether it needs `reencrypt`)",
                        String::from_utf8_lossy(git_path));
                }
                Ok(input)
            },
            (Err(Refusal::Foreign), _) => Err("the committed file is not v3 ciphertext (it was stored without the \
                filter); refusing to present it as a protected file".into()),
            (Err(_), _) => Err(TOO_LARGE.into()),
        }
    }
}

/// The stored key with the config it was unlocked for (whatever the
/// worktree's config is), read from disk at most once per process.
enum StoredKey {
    NotRead,
    Absent,
    Present(Key),
}

impl StoredKey {
    fn get(&mut self, root: &Path) -> Result<Option<&Key>, String> {
        if let StoredKey::NotRead = self {
            *self = match Key::stored(root)? { Some(key) => StoredKey::Present(key), None => StoredKey::Absent };
        }
        Ok(match self { StoredKey::Present(key) => Some(key), _ => None })
    }
}
