//! Exact v3 cryptographic primitives: Argon2id and deterministic AES-256-CMAC-SIV.
//!
//! This crate only *implements* the `V3Primitives` and `V3KeySchedule`
//! traits of `transcrypt-v3-core` and derives keys. Every protocol decision
//! (path policy, configuration authentication, which key a configuration is
//! used with, envelope, configuration binding, release of plaintext) is made
//! by the Aeneas-extracted core functions it calls. Files are sealed and
//! opened only through a `ValidatedKey`.
//! Assumes RustCrypto primitive correctness. Research prototype, not audited.

use aes_siv::{siv::Aes256Siv, KeyInit, Tag};
use argon2::{Algorithm, Argon2, Block, Params, Version};
use sha2::{Digest, Sha256};
pub use transcrypt_v3_core::{StoredKey, MAX_FILE, MAX_PATH, MAX_RECORD};
use transcrypt_v3_core::{
    Refusal, V3KeySchedule, V3Primitives, CONFIG_LEN, CONFIG_PREFIX_LEN, FILE_MIN_LEN, ID_LEN, KEY_FILE_LEN, SALT_LEN,
    TAG_LEN,
};
use zeroize::Zeroizing;

/// Bytes in a kibibyte and in a mebibyte.
pub const KIB: usize = 1024;
pub const MIB: usize = 1024 * KIB;

/// Argon2id memory: 64 MiB, in the KiB units Argon2 counts.
pub const ARGON_MEMORY_KIB: u32 = 65_536;
const _: () = assert!(ARGON_MEMORY_KIB as usize * KIB == 64 * MIB);
pub const ARGON_PASSES: u32 = 3;
pub const ARGON_LANES: u32 = 1;
pub const KEY_SIZE: usize = 64;
const CONFIG_DOMAIN: &[u8] = b"transcrypt/v3/config";
const FILE_DOMAIN: &[u8] = b"transcrypt/v3/file";

pub type SecretKey = Zeroizing<[u8; KEY_SIZE]>;

pub fn derive_key(password: &[u8], salt: &[u8; SALT_LEN]) -> Result<SecretKey, String> {
    if password.is_empty() {
        return Err("empty passphrase refused".into());
    }
    let params = Params::new(ARGON_MEMORY_KIB, ARGON_PASSES, ARGON_LANES, Some(KEY_SIZE))
        .map_err(|_| "unsupported fixed Argon2id parameters")?;
    // Argon2 frees its own working memory without wiping it, and those 64
    // MiB determine the key. Supply memory that is zeroed when dropped.
    let mut memory = Zeroizing::new(vec![Block::default(); params.block_count()]);
    let kdf = Argon2::new(Algorithm::Argon2id, Version::V0x13, params);
    let mut key = Zeroizing::new([0u8; KEY_SIZE]);
    kdf.hash_password_into_with_memory(password, salt, &mut key[..], &mut memory[..])
        .map_err(|_| "Argon2id failed")?;
    Ok(key)
}

/// RustCrypto realization of the core's cryptographic contract under one
/// key. It holds its own copy of the key, on the heap (so that the agent can
/// lock that page in memory) and wiped when dropped.
pub struct Keyed {
    key: Box<SecretKey>,
}

impl Keyed {
    pub fn new(key: &[u8; KEY_SIZE]) -> Self {
        let mut held = Box::new(Zeroizing::new([0u8; KEY_SIZE]));
        held.copy_from_slice(key);
        Keyed { key: held }
    }

    fn siv(&self) -> Option<Aes256Siv> {
        Aes256Siv::new_from_slice(&self.key[..]).ok()
    }
}

/// `from_key(k)` holds exactly the bytes `k` (assumption A17: it realizes
/// the contract under them, A5).
impl V3KeySchedule for Keyed {
    fn from_key(key: &[u8]) -> Option<Self> {
        <&[u8; KEY_SIZE]>::try_from(key).ok().map(Keyed::new)
    }
}

impl V3Primitives for Keyed {
    fn seal_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &mut [u8; TAG_LEN]) -> bool {
        let headers: [&[u8]; 2] = [CONFIG_DOMAIN, prefix];
        match self.siv().map(|mut siv| siv.encrypt(headers, &[])) {
            Some(Ok(sealed)) if sealed.len() == TAG_LEN => {
                tag.copy_from_slice(&sealed);
                true
            }
            _ => false,
        }
    }

    fn open_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &[u8; TAG_LEN]) -> bool {
        // The tag is the AES-SIV encryption of the empty plaintext, so
        // verifying it is opening it; the library compares in constant time.
        let headers: [&[u8]; 2] = [CONFIG_DOMAIN, prefix];
        matches!(self.siv().map(|mut siv| siv.decrypt(headers, tag)), Some(Ok(pt)) if pt.is_empty())
    }

    /// Encrypts in place in the caller's buffer: the plaintext is copied
    /// once into `out[TAG_LEN..]` and overwritten there by the keystream, so
    /// no heap copy of it is left behind.
    fn seal_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], plaintext: &[u8], out: &mut [u8]) -> bool {
        if out.len() != plaintext.len() + TAG_LEN {
            return false;
        }
        let headers: [&[u8]; 3] = [FILE_DOMAIN, config, path];
        let Some(mut siv) = self.siv() else { return false };
        let (tag_out, body) = out.split_at_mut(TAG_LEN);
        body.copy_from_slice(plaintext);
        match siv.encrypt_inout_detached(headers, body.into()) {
            Ok(tag) => {
                tag_out.copy_from_slice(&tag);
                true
            }
            Err(_) => {
                body.fill(0);
                false
            }
        }
    }

    /// Decrypts in place in the caller's buffer. On authentication failure
    /// the library re-encrypts the buffer, so it never holds unauthenticated
    /// plaintext afterwards (and the core then zeroes it).
    fn open_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], sealed: &[u8], out: &mut [u8]) -> bool {
        if sealed.len() != out.len() + TAG_LEN {
            return false;
        }
        let headers: [&[u8]; 3] = [FILE_DOMAIN, config, path];
        let Some(mut siv) = self.siv() else { return false };
        let Ok(tag) = Tag::try_from(&sealed[..TAG_LEN]) else { return false };
        out.copy_from_slice(&sealed[TAG_LEN..]);
        siv.decrypt_inout_detached(headers, out.into(), &tag).is_ok()
    }

    fn config_id(&self, config: &[u8; CONFIG_LEN]) -> [u8; ID_LEN] {
        config_id(config)
    }
}

/// The refusal of an input above the v3 plaintext limit.
pub fn too_large() -> String {
    format!("input exceeds the {} MiB v3 size limit", MAX_FILE / MIB)
}

fn refusal(r: Refusal) -> String {
    match r {
        Refusal::Size => return format!("{} or has an invalid length", too_large()),
        Refusal::Path => "v3 requires a canonical Git-relative path that is not .gitattributes, .gitmodules or in .transcrypt/",
        Refusal::Config => "invalid public v3 configuration",
        Refusal::ConfigAuthentication => "incorrect credentials or tampered public v3 configuration",
        Refusal::Envelope => "invalid v3 ciphertext envelope",
        Refusal::ConfigMismatch => "v3 ciphertext belongs to different public configuration",
        Refusal::Authentication => "v3 ciphertext authentication failed",
        Refusal::DoubleEncryption => "input already is v3 ciphertext; refusing double encryption",
        Refusal::Primitive => "AES-SIV primitive failed",
        Refusal::UnexpectedWorktree => "protected worktree differs from staged ciphertext and its plaintext",
        Refusal::Request => "unsupported agent request",
        Refusal::Index => "malformed or unmerged Git index entry",
        Refusal::Attribute => "unexpected git check-attr output",
        Refusal::Foreign => "not a v3 record of this configuration",
    }
    .into()
}

/// The error for bytes that are no v3 configuration.
pub fn invalid_config() -> String {
    refusal(Refusal::Config)
}

/// A canonical Git-relative name is part of the authenticated cryptographic
/// context. The policy itself is `transcrypt_v3_core::is_canonical_protected_path`.
pub fn validate_protected_path(path: &[u8]) -> Result<(), String> {
    if transcrypt_v3_core::is_canonical_protected_path(path) {
        Ok(())
    } else {
        Err(refusal(Refusal::Path))
    }
}

/// Exact fixed-length view of a public configuration.
pub fn config_array(config_bytes: &[u8]) -> Result<&[u8; CONFIG_LEN], String> {
    config_bytes.try_into().map_err(|_| invalid_config())
}

pub fn config_id(config_bytes: &[u8]) -> [u8; ID_LEN] {
    let digest = Sha256::digest(config_bytes);
    let mut id = [0u8; ID_LEN];
    id.copy_from_slice(&digest[..ID_LEN]);
    id
}

/// A key with the one public configuration it authenticated, and the
/// primitives built from it: the only way this crate seals or opens a file.
///
/// Its fields are private, and every constructor obtains the primitives from
/// the verified `authenticate_key` (directly, or through
/// `unlock_stored_key`), which builds them from exactly the key bytes given
/// and returns them only if they authenticate the configuration kept with
/// them. So a key is never paired with a configuration it did not
/// authenticate, and its configuration cannot be replaced afterwards:
///
/// ```compile_fail,E0451
/// let key = transcrypt_rs::ValidatedKey { config: [0; 55], keyed: transcrypt_rs::Keyed::new(&[0; 64]) };
/// ```
pub struct ValidatedKey {
    config: [u8; CONFIG_LEN],
    keyed: Keyed,
}

impl ValidatedKey {
    /// The key `key`, if it authenticates `config_bytes`.
    pub fn authenticate(config_bytes: &[u8], key: &[u8; KEY_SIZE]) -> Result<Self, String> {
        let config = *config_array(config_bytes)?;
        let keyed = transcrypt_v3_core::authenticate_key::<Keyed>(key, &config).map_err(refusal)?;
        Ok(ValidatedKey { config, keyed })
    }

    /// The key `password` derives for `config_bytes` (with its salt), if it
    /// authenticates it.
    pub fn unlock(password: &[u8], config_bytes: &[u8]) -> Result<Self, String> {
        let config = transcrypt_v3_core::parse_config(config_bytes).map_err(|_| invalid_config())?;
        ValidatedKey::authenticate(config_bytes, &*derive_key(password, &config.salt)?)
    }

    /// A new configuration for `password` and `salt`, with its key.
    pub fn initialize(password: &[u8], salt: &[u8; SALT_LEN]) -> Result<Self, String> {
        let key = derive_key(password, salt)?;
        let config = transcrypt_v3_core::initialize_config(&Keyed::new(&key), salt).map_err(refusal)?;
        ValidatedKey::authenticate(&config, &key)
    }

    /// The stored key for configuration `current`, as the verified
    /// `unlock_stored_key` decides from the key file's bytes `file` (if
    /// `present`): only for a file holding exactly `current`, a key that
    /// authenticates it, and that key's check value for it, and then with
    /// that key. Otherwise the state (`Absent`, `Damaged` or `Stale`).
    pub fn from_stored(present: bool, file: &[u8], current: &[u8]) -> Result<Self, StoredKey> {
        transcrypt_v3_core::unlock_stored_key::<Keyed>(present, file, current)
            .map(|(keyed, config)| ValidatedKey { config, keyed })
    }

    /// The stored key file of this key (`from_stored` reads it back): the
    /// configuration, the key, and the key's check value for the
    /// configuration, which the verified `seal_key_check` computes. The
    /// configuration tag depends on only half of the AES-SIV key; the check
    /// value, a sealed nonempty constant, involves all of it.
    pub fn to_stored(&self) -> Result<Zeroizing<Vec<u8>>, String> {
        let check = transcrypt_v3_core::seal_key_check(&self.keyed, &self.config).map_err(refusal)?;
        let mut file = Zeroizing::new(Vec::with_capacity(KEY_FILE_LEN));
        file.extend_from_slice(&self.config);
        file.extend_from_slice(&self.keyed.key[..]);
        file.extend_from_slice(&check);
        Ok(file)
    }

    /// The configuration this key authenticated.
    pub fn config(&self) -> &[u8; CONFIG_LEN] {
        &self.config
    }

    /// The public identifier of this key's configuration (records name it).
    pub fn config_id(&self) -> [u8; ID_LEN] {
        config_id(&self.config)
    }

    /// The key bytes, to store them or to hand them to the private agent.
    pub fn secret(&self) -> &[u8; KEY_SIZE] {
        &self.keyed.key
    }

    /// The record of `plaintext` at `path`.
    pub fn encrypt(&self, path: &[u8], plaintext: &[u8]) -> Result<Vec<u8>, String> {
        if plaintext.len() > MAX_FILE {
            return Err(refusal(Refusal::Size));
        }
        let mut out = vec![0u8; plaintext.len() + FILE_MIN_LEN];
        transcrypt_v3_core::seal_record(&self.keyed, &self.config, path, plaintext, &mut out).map_err(refusal)?;
        Ok(out)
    }

    /// The clean filter. Git expects filters to be idempotent (it re-cleans
    /// a worktree file whenever its cached stat data is stale, including a
    /// worktree that `lock` just reset to ciphertext). A record that already
    /// opens at this path under this configuration is returned unchanged: by
    /// determinism it is exactly what sealing its plaintext produces, so the
    /// result is the same as decrypting and re-encrypting. Everything else
    /// is sealed by the verified core, which still refuses any other v3
    /// record.
    pub fn clean(&self, path: &[u8], input: &[u8]) -> Result<Vec<u8>, String> {
        // Only a record can open: parsing its header first spares ordinary
        // plaintext a decryption attempt (and its output buffer).
        if transcrypt_v3_core::parse_file_header(input).is_ok() && self.decrypt(path, input).is_ok() {
            return Ok(input.to_vec());
        }
        self.encrypt(path, input)
    }

    /// Authenticate `record` at `path` and return its plaintext.
    pub fn decrypt(&self, path: &[u8], record: &[u8]) -> Result<Zeroizing<Vec<u8>>, String> {
        if record.len() > MAX_RECORD {
            return Err(refusal(Refusal::Size));
        }
        let mut out = Zeroizing::new(vec![0u8; record.len().saturating_sub(FILE_MIN_LEN)]);
        transcrypt_v3_core::open_record(&self.keyed, &self.config, path, record, &mut out).map_err(refusal)?;
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use transcrypt_v3_core::KEY_CHECK_START;

    const PASSPHRASE: &[u8] = b"correct horse battery staple long secret";

    fn fixture() -> ValidatedKey {
        let salt = [7u8; SALT_LEN];
        ValidatedKey::initialize(PASSPHRASE, &salt).unwrap()
    }

    /// A stored key file for `config`: the config, the key, then the check
    /// value `check`.
    fn key_file(config: &[u8], key: &[u8], check: &[u8]) -> Vec<u8> {
        [config, key, check].concat()
    }

    /// The check value of `key`'s file.
    fn check_of(key: &ValidatedKey) -> Vec<u8> {
        key.to_stored().unwrap()[KEY_CHECK_START..].to_vec()
    }

    #[test]
    fn complete_lifecycle_and_determinism() {
        let v = fixture();
        let v2 = ValidatedKey::unlock(PASSPHRASE, v.config()).unwrap();
        assert_eq!(&v.secret()[..], &v2.secret()[..]);
        assert_eq!(v.config(), v2.config());
        assert!(ValidatedKey::unlock(b"bad password", v.config()).is_err());
        for plaintext in [b"".as_slice(), b"hello".as_slice(), &[0, 1, 255, 0][..]] {
            let ct1 = v.encrypt(b"safe/item.secret", plaintext).unwrap();
            let ct2 = v.encrypt(b"safe/item.secret", plaintext).unwrap();
            assert_eq!(ct1, ct2);
            assert_eq!(&v.decrypt(b"safe/item.secret", &ct1).unwrap()[..], plaintext);
            let mut corrupt = ct1.clone();
            let last = corrupt.len() - 1;
            corrupt[last] ^= 1;
            assert!(v.decrypt(b"safe/item.secret", &corrupt).is_err());
        }
    }

    #[test]
    fn clean_is_idempotent_and_still_refuses_foreign_records() {
        let v = fixture();
        let record = v.encrypt(b"a.secret", b"payload").unwrap();
        assert_eq!(v.clean(b"a.secret", b"payload").unwrap(), record);
        assert_eq!(v.clean(b"a.secret", &record).unwrap(), record);
        // The same record at another path, or tampered, is not authentic there.
        assert!(v.clean(b"b.secret", &record).is_err());
        let mut tampered = record.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 1;
        assert!(v.clean(b"a.secret", &tampered).is_err());
    }

    #[test]
    fn config_binding_and_fail_closed() {
        let v = fixture();
        let ct = v.encrypt(b"account.secret", b"private").unwrap();
        let mut altered = *v.config();
        altered[7] ^= 0x40;
        // The key does not authenticate the altered config, so no validated
        // key for it exists; and the core refuses it on every operation.
        assert!(ValidatedKey::authenticate(&altered, v.secret()).is_err());
        let mut out = vec![0u8; ct.len() - FILE_MIN_LEN];
        assert_eq!(transcrypt_v3_core::open_record(&Keyed::new(v.secret()), &altered, b"account.secret", &ct, &mut out),
            Err(Refusal::ConfigAuthentication));
        let mut altered_ct = ct.clone();
        altered_ct[0] = 0;
        assert!(v.decrypt(b"account.secret", &altered_ct).is_err());
        assert!(v.decrypt(b"account.secret", b"private").is_err());
    }

    #[test]
    fn ciphertext_is_bound_to_exact_git_path() {
        let v = fixture();
        let original = v.encrypt(b"vault/a.secret", b"identical").unwrap();
        let repeated = v.encrypt(b"vault/a.secret", b"identical").unwrap();
        let different = v.encrypt(b"vault/b.secret", b"identical").unwrap();
        assert_eq!(original, repeated, "Git determinism must be preserved within a path");
        assert_ne!(original, different, "distinct Git paths must use distinct SIV AD");
        assert_eq!(&v.decrypt(b"vault/a.secret", &original).unwrap()[..], b"identical");
        assert!(v.decrypt(b"vault/b.secret", &original).is_err());
        assert!(v.decrypt(b"a.secret", &original).is_err());
        assert!(v.decrypt(b"vault/a.secret", &different).is_err());
    }

    #[test]
    fn raw_unix_paths_are_bound_and_noncanonical_inputs_fail_closed() {
        let v = fixture();
        for path in [b"a b.secret".as_slice(), b"a'quote.secret", b"dir/new\nline.secret", b"raw/\xff.secret"] {
            let record = v.encrypt(path, b"payload").unwrap();
            assert_eq!(&v.decrypt(path, &record).unwrap()[..], b"payload");
        }
        for path in [b"".as_slice(), b".gitattributes", b"/root.secret", b"../bad.secret", b"x/../bad.secret", b"./x.secret", b"x//y.secret", b"x/./y.secret", b"x.secret/", b"evil\0.secret"] {
            assert!(validate_protected_path(path).is_err(), "accepted {:?}", path);
        }
        assert!(validate_protected_path(&std::vec![b'x'; MAX_PATH + 1]).is_err());
    }

    /// A validated key is the stored file's own key, for exactly the
    /// configuration that file names and the key authenticates; never a key
    /// from another configuration or credential source.
    #[test]
    fn stored_keys_validate_only_their_own_authentic_config() {
        let a = fixture();
        let b = ValidatedKey::initialize(PASSPHRASE, &[8u8; SALT_LEN]).unwrap();
        assert_ne!(a.config(), b.config());
        // The file `store` writes: the config, the key, its check value.
        let file_a = a.to_stored().unwrap();
        assert_eq!(file_a.len(), KEY_FILE_LEN);
        assert_eq!(&file_a[..KEY_CHECK_START], &key_file(a.config(), a.secret(), &[])[..]);
        // The file of A while the current config is B: stale, no key.
        assert!(matches!(ValidatedKey::from_stored(true, &file_a, b.config()), Err(StoredKey::Stale)));
        // B's config with A's key (and either check value): the prefix
        // matches, the key does not authenticate it.
        for check in [check_of(&a), check_of(&b)] {
            let spliced = key_file(b.config(), a.secret(), &check);
            assert!(matches!(ValidatedKey::from_stored(true, &spliced, b.config()), Err(StoredKey::Stale)));
        }
        // A's config and key with B's check value: the key authenticates
        // the config, but the check value is not its own.
        let spliced = key_file(a.config(), a.secret(), &check_of(&b));
        assert!(matches!(ValidatedKey::from_stored(true, &spliced, a.config()), Err(StoredKey::Stale)));
        // Every single-bit change of the key or of its check value is
        // refused, including in the CTR half of the key (RFC 5297:
        // key[KEY_SIZE / 2..]), which the config tag, the encryption of
        // the empty plaintext, does not depend on: the check value, the
        // encryption of a nonempty constant, does. So a damaged key never
        // seals records the genuine key would refuse.
        const BITS: usize = u8::BITS as usize;
        for bit in 0..((KEY_FILE_LEN - CONFIG_LEN) * BITS) {
            let mut flipped = file_a.clone();
            flipped[CONFIG_LEN + bit / BITS] ^= 1 << (bit % BITS);
            let state = ValidatedKey::from_stored(true, &flipped, a.config());
            assert!(matches!(state, Err(StoredKey::Stale)), "bit {bit}");
        }
        // A file of the earlier layout (the config and the key, without a
        // check value) is damaged: `unlock` rewrites it.
        let earlier = key_file(a.config(), a.secret(), &[]);
        assert!(matches!(ValidatedKey::from_stored(true, &earlier, a.config()), Err(StoredKey::Damaged)));
        // The genuine file: its key, for the config it names.
        let stored = ValidatedKey::from_stored(true, &file_a, a.config()).unwrap();
        assert_eq!(stored.config(), a.config());
        assert_eq!(&stored.secret()[..], &file_a[CONFIG_LEN..KEY_CHECK_START]);
        assert_eq!(stored.to_stored().unwrap(), file_a);
        let record = stored.encrypt(b"x.secret", b"payload").unwrap();
        assert_eq!(record, a.encrypt(b"x.secret", b"payload").unwrap());
        assert!(b.decrypt(b"x.secret", &record).is_err());
        // No file, a bare key (an earlier version's), other lengths, or a
        // current config of the wrong length.
        assert!(matches!(ValidatedKey::from_stored(false, &file_a, a.config()), Err(StoredKey::Absent)));
        assert!(matches!(ValidatedKey::from_stored(true, &a.secret()[..], a.config()), Err(StoredKey::Absent)));
        for len in [0, 1, CONFIG_LEN, KEY_CHECK_START, KEY_FILE_LEN - 1, KEY_FILE_LEN + 1] {
            let mut damaged = file_a.clone();
            damaged.resize(len, 0);
            assert!(matches!(ValidatedKey::from_stored(true, &damaged, a.config()), Err(StoredKey::Damaged)), "{len}");
        }
        assert!(matches!(ValidatedKey::from_stored(true, &file_a, &a.config()[1..]), Err(StoredKey::Stale)));
        // Keys from passphrases: only for the config they authenticate.
        assert!(ValidatedKey::authenticate(b.config(), a.secret()).is_err());
        assert!(ValidatedKey::authenticate(&a.config()[1..], a.secret()).is_err());
        assert!(ValidatedKey::unlock(b"another long passphrase", a.config()).is_err());
        // The key schedule takes exactly the key bytes.
        assert!(Keyed::from_key(&a.secret()[1..]).is_none());
        assert!(Keyed::from_key(&file_a).is_none());
    }


    /// Each clause of the Lean `Realizes` contract (assumption A5) checked
    /// directly on the production `Keyed` primitive, over many lengths,
    /// paths and single-bit tamperings. Byte-exactness against an
    /// independent implementation is covered by `tests/v3_vectors.rs`.
    #[test]
    fn keyed_satisfies_the_realizes_contract() {
        let v = fixture();
        let keyed = Keyed::new(v.secret());
        let config: [u8; CONFIG_LEN] = *v.config();
        // seal_config / open_config agree, and the stored tag is the seal.
        let prefix: [u8; CONFIG_PREFIX_LEN] = config[..CONFIG_PREFIX_LEN].try_into().unwrap();
        let mut tag = [0u8; TAG_LEN];
        assert!(keyed.seal_config(&prefix, &mut tag));
        assert_eq!(&tag[..], &config[CONFIG_PREFIX_LEN..]);
        assert!(keyed.open_config(&prefix, &tag));
        const BITS: usize = u8::BITS as usize;
        for bit in 0..(TAG_LEN * BITS) {
            let mut bad = tag;
            bad[bit / BITS] ^= 1 << (bit % BITS);
            assert!(!keyed.open_config(&prefix, &bad));
        }
        // config_id is the keyless SHA-256 truncation.
        assert_eq!(keyed.config_id(&config), Sha256::digest(config)[..ID_LEN]);
        // Marsaglia's xorshift64 (shifts 13, 7, 17) from a fixed seed.
        const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
        const SHIFTS: (u32, u32, u32) = (13, 7, 17);
        let mut state = SEED;
        let mut next = || { state ^= state << SHIFTS.0; state ^= state >> SHIFTS.1; state ^= state << SHIFTS.2; state };
        // Lengths around one AES block (the tag length) and a few others.
        for len in [0usize, 1, TAG_LEN - 1, TAG_LEN, TAG_LEN + 1, 255, 1000] {
            let pt: Vec<u8> = (0..len).map(|_| next() as u8).collect();
            let path = format!("d{}/f.secret", next() % 7);
            let mut sealed = vec![0u8; len + TAG_LEN];
            assert!(keyed.seal_file(&config, path.as_bytes(), &pt, &mut sealed));
            assert_eq!(sealed.len(), len + TAG_LEN, "length preserved");
            // Completeness: a genuine sealing of a right-sized plaintext opens to it.
            let mut out = vec![0xaau8; len];
            assert!(keyed.open_file(&config, path.as_bytes(), &sealed, &mut out));
            assert_eq!(out, pt);
            // Soundness: wrong output size, wrong path or config, or any tampering fails.
            assert!(!keyed.open_file(&config, path.as_bytes(), &sealed, &mut vec![0u8; len + 1]));
            assert!(!keyed.seal_file(&config, path.as_bytes(), &pt, &mut vec![0u8; len + TAG_LEN + 1]));
            assert!(!keyed.open_file(&config, b"other.secret", &sealed, &mut out));
            let mut other = config;
            other[CONFIG_LEN - 1] ^= 1;
            assert!(!keyed.open_file(&other, path.as_bytes(), &sealed, &mut out));
            let flip = (next() as usize) % (sealed.len() * BITS);
            let mut tampered = sealed.clone();
            tampered[flip / BITS] ^= 1 << (flip % BITS);
            assert!(!keyed.open_file(&config, path.as_bytes(), &tampered, &mut out));
            // Determinism: the same inputs seal to the same bytes.
            let mut again = vec![0u8; len + TAG_LEN];
            assert!(keyed.seal_file(&config, path.as_bytes(), &pt, &mut again));
            assert_eq!(again, sealed);
        }
    }
}
