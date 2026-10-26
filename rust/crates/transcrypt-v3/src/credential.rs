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
use transcrypt_v3::{authenticate_config, clean_file, decrypt_file, SecretKey, KEY_SIZE};
use transcrypt_v3_core::{CONFIG_LEN, ID_LEN};
use crate::{fsat, session::{self, Operation}};

const KEY_FILE: &str = "key";

/// An unlocked key for one public configuration.
pub(crate) struct Key {
    root: PathBuf,
    config: Vec<u8>,
    stored: Option<SecretKey>,
}

/// What `Key::state` found.
pub(crate) enum State {
    /// A stored key or a running agent for this configuration.
    Unlocked { private: bool },
    /// No credential.
    Locked,
    /// A stored key that does not authenticate this configuration: the
    /// committed config changed (a pulled `rekey`), or the file is damaged.
    Stale,
}

impl Key {
    /// The key for `config`, if this checkout is unlocked for it.
    pub(crate) fn load(root: &Path, config: &[u8]) -> Result<Option<Key>, String> {
        Ok(lookup(root, config)?.1)
    }

    /// Like `load`, but required: the error says how to unlock.
    pub(crate) fn require(root: &Path, config: &[u8]) -> Result<Key, String> {
        match lookup(root, config)? {
            (_, Some(key)) => Ok(key),
            (State::Stale, None) => Err("the stored key does not match .transcrypt/config (it was rekeyed?); \
                run `transcrypt-v3 unlock` with the current passphrase".into()),
            _ => Err("this checkout is locked; run `transcrypt-v3 unlock`".into()),
        }
    }

    /// The stored key with the config it was unlocked for, whatever the
    /// worktree's config is now (during a checkout, Git may write files
    /// before it writes `.transcrypt/config`).
    pub(crate) fn stored(root: &Path) -> Result<Option<Key>, String> {
        let Some((config, key)) = read_stored(root)? else { return Ok(None) };
        if authenticate_config(&config, &key).is_err() { return Ok(None); }
        Ok(Some(Key { root: root.to_owned(), config, stored: Some(key) }))
    }

    /// The public identifier of this key's config (records name it).
    pub(crate) fn config_id(&self) -> [u8; ID_LEN] {
        transcrypt_v3::config_id(&self.config)
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
            None => session::request(&self.root, &self.config, Operation::Encrypt, path, input),
        }
    }

    /// Authenticate `record` at `path` and return its plaintext.
    pub(crate) fn open(&self, path: &[u8], record: &[u8]) -> Result<Zeroizing<Vec<u8>>, String> {
        match &self.stored {
            Some(key) => decrypt_file(&self.config, key, path, record),
            None => session::request(&self.root, &self.config, Operation::Decrypt, path, record),
        }
    }
}

/// How this checkout is unlocked for `config`.
pub(crate) fn state(root: &Path, config: &[u8]) -> Result<State, String> {
    Ok(lookup(root, config)?.0)
}

/// How this checkout is unlocked for `config`, with the key when it is.
pub(crate) fn lookup(root: &Path, config: &[u8]) -> Result<(State, Option<Key>), String> {
    let key = |stored| Some(Key { root: root.to_owned(), config: config.to_vec(), stored });
    if let Some((stored_config, secret)) = read_stored(root)? {
        return Ok(if stored_config == config && authenticate_config(config, &secret).is_ok() {
            (State::Unlocked { private: false }, key(Some(secret)))
        } else {
            (State::Stale, None)
        });
    }
    Ok(if session::request(root, config, Operation::Ping, &[], &[]).is_ok() {
        (State::Unlocked { private: true }, key(None))
    } else {
        (State::Locked, None)
    })
}

/// The stored config and key, if there are any. A key file that is not a
/// regular file of exactly that size, in the checked private directory, is
/// an error.
fn read_stored(root: &Path) -> Result<Option<(Vec<u8>, SecretKey)>, String> {
    let Some(dir) = session::existing_directory(root)? else { return Ok(None) };
    let dir = fsat::Dir::open(&dir).map_err(|_| "cannot open the local v3 credential directory")?;
    let mut file = match dir.open_regular(OsStr::new(KEY_FILE)) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(_) => return Err("unsafe .git/transcrypt-v3/key: expected a regular file".into()),
    };
    // A key stored by an earlier version (the key alone, without its
    // config) is not used: the checkout counts as locked until `unlock`
    // replaces it.
    if file.metadata().is_ok_and(|m| m.len() == KEY_SIZE as u64) { return Ok(None); }
    let mut config = vec![0u8; CONFIG_LEN];
    let mut key: SecretKey = Zeroizing::new([0u8; KEY_SIZE]);
    let mut extra = [0u8; 1];
    if file.read_exact(&mut config).is_err() || file.read_exact(&mut key[..]).is_err()
        || !matches!(file.read(&mut extra), Ok(0))
    {
        return Err("damaged .git/transcrypt-v3/key; run `transcrypt-v3 unlock` again".into());
    }
    Ok(Some((config, key)))
}

/// Store `key`, with the public `config` it unlocks, for later commands: an
/// exclusive 0600 temporary in the private directory, synced, then renamed
/// over any previous key.
pub(crate) fn store(root: &Path, config: &[u8], key: &SecretKey) -> Result<(), String> {
    if config.len() != CONFIG_LEN { return Err("invalid public v3 configuration".into()); }
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
