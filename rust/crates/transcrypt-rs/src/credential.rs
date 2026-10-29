//! Where an unlocked checkout keeps its key, and the one interface every
//! filter and command uses to encrypt and decrypt with it.
//!
//! - **Stored** (the default): `unlock` writes the derived key, never the
//!   passphrase, with the public config it unlocks, to
//!   `.git/transcrypt-v3/key` (mode 0600 in a 0700 directory
//!   shared by all worktrees, never committed and not in `git config`). Git
//!   commands then work without prompting, across shells and reboots, with
//!   no background process. Whoever can read that file can decrypt this
//!   repository, exactly like whoever can read the unlocked checkout.
//! - **Private** (`unlock --private`): the key lives only in the memory of a
//!   credential agent (`session.rs`) until `lock` or logout, and plaintext
//!   written to the worktree is made private to this user.
//!
//! Both produce byte-identical records: the key and the verified core are
//! the same; only where the key waits between commands differs.

use std::{
    ffi::OsStr,
    io::{self, Read, Write},
    path::{Path, PathBuf},
};
use zeroize::Zeroizing;
use transcrypt_rs::{authenticate_config, clean_file, decrypt_file, SecretKey, KEY_SIZE};
use transcrypt_v3_core::{stored_key_state, AgentOp, StoredKey, CONFIG_LEN, ID_LEN, KEY_FILE_LEN};
use crate::{fsat, session};

const KEY_FILE: &str = "key";
const DAMAGED: &str = "damaged .git/transcrypt-v3/key; run `transcrypt-rs unlock` again";
// The verified decision's layout is this adapter's: the config, then the key.
const _: () = assert!(KEY_FILE_LEN == CONFIG_LEN + KEY_SIZE && transcrypt_v3_core::KEY_LEN == KEY_SIZE);

/// An unlocked key for one public configuration.
pub(crate) struct Key {
    root: PathBuf,
    config: Vec<u8>,
    stored: Option<SecretKey>,
}

/// How this checkout is unlocked for a configuration (`lookup`).
pub(crate) enum Unlock {
    /// A stored key or a running agent for this configuration.
    Unlocked(Key),
    /// No credential.
    Locked,
    /// A stored key that does not authenticate this configuration: the
    /// committed config changed (a pulled `rekey`), or the file is damaged.
    Stale,
}

impl Unlock {
    /// The key, when unlocked.
    pub(crate) fn key(&self) -> Option<&Key> {
        match self { Unlock::Unlocked(key) => Some(key), _ => None }
    }
}

impl Key {
    /// The key for `config`, if this checkout is unlocked for it.
    pub(crate) fn load(root: &Path, config: &[u8]) -> Result<Option<Key>, String> {
        Ok(match lookup(root, config)? { Unlock::Unlocked(key) => Some(key), _ => None })
    }

    /// Like `load`, but required: the error says how to unlock.
    pub(crate) fn require(root: &Path, config: &[u8]) -> Result<Key, String> {
        match lookup(root, config)? {
            Unlock::Unlocked(key) => Ok(key),
            Unlock::Stale => Err("the stored key does not match .transcrypt/config (it was rekeyed?); \
                run `transcrypt-rs unlock` with the current passphrase".into()),
            Unlock::Locked => Err("this checkout is locked; run `transcrypt-rs unlock`".into()),
        }
    }

    /// The stored key with the config it was unlocked for, whatever the
    /// worktree's config is now (during a checkout, Git may write files
    /// before it writes `.transcrypt/config`).
    pub(crate) fn stored(root: &Path) -> Result<Option<Key>, String> {
        let file = read_key_file(root)?;
        let file = file.as_ref().map(|f| f.as_slice());
        let stored_config = file.and_then(|f| f.get(..CONFIG_LEN)).unwrap_or_default();
        match stored_lookup(file, stored_config) {
            Ok(Some(secret)) => Ok(Some(Key { root: root.to_owned(), config: stored_config.to_vec(), stored: Some(secret) })),
            Ok(None) | Err(StoredKey::Stale) => Ok(None),
            Err(_) => Err(DAMAGED.into()),
        }
    }

    /// The public identifier of this key's config (records name it).
    pub(crate) fn config_id(&self) -> [u8; ID_LEN] {
        transcrypt_rs::config_id(&self.config)
    }

    /// Whether this is the private mode (in-memory agent, private files).
    pub(crate) fn private(&self) -> bool {
        self.stored.is_none()
    }

    /// The clean filter: the record for `input` at `path` (an input that
    /// already is that genuine record is returned unchanged).
    pub(crate) fn clean(&self, path: &[u8], input: &[u8]) -> Result<Zeroizing<Vec<u8>>, String> {
        match &self.stored {
            Some(key) => clean_file(&self.config, key, path, input).map(Zeroizing::new),
            None => session::request(&self.root, &self.config, AgentOp::Encrypt, path, input),
        }
    }

    /// Authenticate `record` at `path` and return its plaintext.
    pub(crate) fn open(&self, path: &[u8], record: &[u8]) -> Result<Zeroizing<Vec<u8>>, String> {
        match &self.stored {
            Some(key) => decrypt_file(&self.config, key, path, record),
            None => session::request(&self.root, &self.config, AgentOp::Decrypt, path, record),
        }
    }
}

/// `lookup`, for `unlock`: a damaged stored key counts as locked, since
/// unlocking replaces it. Every other command refuses it.
pub(crate) fn state_to_unlock(root: &Path, config: &[u8]) -> Result<Unlock, String> {
    let file = read_key_file(root)?;
    match stored_lookup(file.as_ref().map(|f| f.as_slice()), config) {
        Err(StoredKey::Damaged) => Ok(Unlock::Locked),
        stored => unlock_state(root, config, stored),
    }
}

/// How this checkout is unlocked for `config`, with the key when it is.
pub(crate) fn lookup(root: &Path, config: &[u8]) -> Result<Unlock, String> {
    let file = read_key_file(root)?;
    unlock_state(root, config, stored_lookup(file.as_ref().map(|f| f.as_slice()), config))
}

/// `lookup` given what the stored key file holds: without a stored key, the
/// private agent is asked.
fn unlock_state(root: &Path, config: &[u8], stored: Result<Option<SecretKey>, StoredKey>) -> Result<Unlock, String> {
    let key = |stored| Key { root: root.to_owned(), config: config.to_vec(), stored };
    match stored {
        Ok(Some(secret)) => return Ok(Unlock::Unlocked(key(Some(secret)))),
        Err(StoredKey::Stale) => return Ok(Unlock::Stale),
        Err(_) => return Err(DAMAGED.into()),
        Ok(None) => {},
    }
    Ok(if session::request(root, config, AgentOp::Ping, &[], &[]).is_ok() {
        Unlock::Unlocked(key(None))
    } else {
        Unlock::Locked
    })
}

/// The stored key for `config`, as the verified `stored_key_state` decides:
/// `Ok(Some)` only if the file holds exactly `config` then a key that
/// authenticates it; `Ok(None)` without a stored key (none, or one written
/// by an earlier version: the key alone); `Err(Stale)` for a key of another
/// config or one that does not authenticate it; `Err(Damaged)` otherwise.
fn stored_lookup(file: Option<&[u8]>, config: &[u8]) -> Result<Option<SecretKey>, StoredKey> {
    let bytes = file.unwrap_or_default();
    // The key bytes, if the file has the stored layout (`config ‖ key`).
    let secret: Option<SecretKey> = (bytes.len() == KEY_FILE_LEN).then(|| {
        let mut key: SecretKey = Zeroizing::new([0u8; KEY_SIZE]);
        key.copy_from_slice(&bytes[CONFIG_LEN..]);
        key
    });
    let authentic = secret.as_ref().is_some_and(|key| authenticate_config(config, key).is_ok());
    match stored_key_state(file.is_some(), bytes, config, authentic) {
        StoredKey::Unlocked => Ok(secret),
        StoredKey::Absent => Ok(None),
        state => Err(state),
    }
}

/// The bytes of the stored key file (at most one more than a valid file
/// holds, in wiped memory), if there is one. A key file that is not a
/// regular file in the checked private directory is an error.
fn read_key_file(root: &Path) -> Result<Option<Zeroizing<Vec<u8>>>, String> {
    let Some(dir) = session::existing_directory(root)? else { return Ok(None) };
    let dir = fsat::Dir::open(&dir).map_err(|_| "cannot open the local v3 credential directory")?;
    let file = match dir.open_regular(OsStr::new(KEY_FILE)) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(_) => return Err("unsafe .git/transcrypt-v3/key: expected a regular file".into()),
    };
    crate::git::read_wiped(&mut file.take(KEY_FILE_LEN as u64 + 1), KEY_FILE_LEN + 1)
        .map(Some).map_err(|_| "cannot read .git/transcrypt-v3/key".into())
}

/// Store `key`, with the public `config` it unlocks, for later commands: an
/// exclusive 0600 temporary in the private directory, synced, then renamed
/// over any previous key.
pub(crate) fn store(root: &Path, config: &[u8], key: &SecretKey) -> Result<(), String> {
    if config.len() != CONFIG_LEN { return Err(transcrypt_rs::invalid_config()); }
    let dir = fsat::Dir::open(&session::prepare_directory(root)?)
        .map_err(|_| "cannot open the local v3 credential directory")?;
    let temp = format!("{KEY_FILE}.{}.tmp", std::process::id());
    let temp = OsStr::new(&temp);
    let _ = dir.unlink(temp);
    let mut file = dir.create_new(temp, 0o600).map_err(|e| format!("cannot create the key file: {e}"))?;
    let written = file.write_all(config).and_then(|_| file.write_all(&key[..])).and_then(|_| file.sync_all());
    drop(file);
    if let Err(e) = written.and_then(|_| dir.rename_to(temp, &dir, OsStr::new(KEY_FILE))) {
        let _ = dir.unlink(temp);
        return Err(format!("cannot store the key: {e}"));
    }
    dir.sync().map_err(|e| format!("cannot sync the credential directory: {e}"))
}

/// Remove the stored key, if any. Returns whether there was one. Not a
/// secure erasure: the file system may keep copies of its blocks.
pub(crate) fn forget(root: &Path) -> Result<bool, String> {
    let Some(dir) = session::existing_directory(root)? else { return Ok(false) };
    let dir = fsat::Dir::open(&dir).map_err(|_| "cannot open the local v3 credential directory")?;
    match dir.unlink(OsStr::new(KEY_FILE)) {
        Ok(()) => dir.sync().map(|_| true).map_err(|e| format!("cannot sync the credential directory: {e}")),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(format!("cannot remove the stored key: {e}")),
    }
}
