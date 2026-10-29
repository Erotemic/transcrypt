//! Exact v3 cryptographic primitives: Argon2id and deterministic AES-256-CMAC-SIV.
//!
//! This crate only *implements* the `V3Primitives` trait of
//! `transcrypt-v3-core` and derives keys. Every protocol decision (path policy,
//! configuration authentication, envelope, configuration binding, release of
//! plaintext) is made by the Aeneas-extracted core functions it calls.
//! Assumes RustCrypto primitive correctness. Research prototype, not audited.

use aes_siv::{siv::Aes256Siv, KeyInit, Tag};
use argon2::{Algorithm, Argon2, Block, Params, Version};
use sha2::{Digest, Sha256};
pub use transcrypt_v3_core::{MAX_FILE, MAX_PATH, MAX_RECORD};
use transcrypt_v3_core::{
    Refusal, V3Primitives, CONFIG_LEN, CONFIG_PREFIX_LEN, FILE_MIN_LEN, ID_LEN, SALT_LEN, TAG_LEN,
};
use zeroize::Zeroizing;

pub const ARGON_MEMORY_KIB: u32 = 65_536;
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

/// RustCrypto realization of the core's cryptographic contract under one key.
pub struct Keyed<'a> {
    key: &'a [u8; KEY_SIZE],
}

impl<'a> Keyed<'a> {
    pub fn new(key: &'a [u8; KEY_SIZE]) -> Self {
        Keyed { key }
    }

    fn siv(&self) -> Option<Aes256Siv> {
        Aes256Siv::new_from_slice(&self.key[..]).ok()
    }
}

impl V3Primitives for Keyed<'_> {
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

fn refusal(r: Refusal) -> String {
    match r {
        Refusal::Path => "v3 requires a canonical Git-relative path that is not .gitattributes, .gitmodules or in .transcrypt/",
        Refusal::Size => "input exceeds the 16 MiB v3 limit or has an invalid length",
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

pub fn initialize_config(password: &[u8], salt: &[u8; SALT_LEN])
    -> Result<([u8; CONFIG_LEN], SecretKey), String>
{
    let key = derive_key(password, salt)?;
    let config = transcrypt_v3_core::initialize_config(&Keyed::new(&key), salt).map_err(refusal)?;
    Ok((config, key))
}

pub fn authenticate_config(config_bytes: &[u8], key: &[u8; KEY_SIZE]) -> Result<(), String> {
    transcrypt_v3_core::authenticate_config(&Keyed::new(key), config_array(config_bytes)?)
        .map(|_| ())
        .map_err(refusal)
}

pub fn unlock_config(password: &[u8], config_bytes: &[u8]) -> Result<SecretKey, String> {
    let config = transcrypt_v3_core::parse_config(config_bytes).map_err(|_| invalid_config())?;
    let key = derive_key(password, &config.salt)?;
    authenticate_config(config_bytes, &key)?;
    Ok(key)
}

pub fn config_id(config_bytes: &[u8]) -> [u8; ID_LEN] {
    let digest = Sha256::digest(config_bytes);
    let mut id = [0u8; ID_LEN];
    id.copy_from_slice(&digest[..ID_LEN]);
    id
}

pub fn encrypt_file(config_bytes: &[u8], key: &[u8; KEY_SIZE], path: &[u8], plaintext: &[u8])
    -> Result<Vec<u8>, String>
{
    if plaintext.len() > MAX_FILE {
        return Err(refusal(Refusal::Size));
    }
    let mut out = vec![0u8; plaintext.len() + FILE_MIN_LEN];
    transcrypt_v3_core::seal_record(&Keyed::new(key), config_array(config_bytes)?, path, plaintext, &mut out)
        .map_err(refusal)?;
    Ok(out)
}

/// Git's clean filter. Git expects filters to be idempotent (it re-cleans
/// a worktree file whenever its cached stat data is stale, including a
/// worktree that `lock` just reset to ciphertext). A record that already
/// opens at this path under this configuration is returned unchanged: by
/// determinism it is exactly what sealing its plaintext produces, so the
/// result is the same as decrypting and re-encrypting. Everything else is
/// sealed by the verified core, which still refuses any other v3 record.
pub fn clean_file(config_bytes: &[u8], key: &[u8; KEY_SIZE], path: &[u8], input: &[u8])
    -> Result<Vec<u8>, String>
{
    if decrypt_file(config_bytes, key, path, input).is_ok() {
        return Ok(input.to_vec());
    }
    encrypt_file(config_bytes, key, path, input)
}

pub fn decrypt_file(config_bytes: &[u8], key: &[u8; KEY_SIZE], path: &[u8], record: &[u8])
    -> Result<Zeroizing<Vec<u8>>, String>
{
    if record.len() > MAX_RECORD {
        return Err(refusal(Refusal::Size));
    }
    let mut out = Zeroizing::new(vec![0u8; record.len().saturating_sub(FILE_MIN_LEN)]);
    transcrypt_v3_core::open_record(&Keyed::new(key), config_array(config_bytes)?, path, record, &mut out)
        .map_err(refusal)?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> ([u8; CONFIG_LEN], SecretKey) {
        let salt = [7u8; SALT_LEN];
        initialize_config(b"correct horse battery staple long secret", &salt).unwrap()
    }

    #[test]
    fn complete_lifecycle_and_determinism() {
        let (config, key) = fixture();
        let key2 = unlock_config(b"correct horse battery staple long secret", &config).unwrap();
        assert_eq!(&key[..], &key2[..]);
        assert!(unlock_config(b"bad password", &config).is_err());
        for plaintext in [b"".as_slice(), b"hello".as_slice(), &[0, 1, 255, 0][..]] {
            let ct1 = encrypt_file(&config, &key, b"safe/item.secret", plaintext).unwrap();
            let ct2 = encrypt_file(&config, &key, b"safe/item.secret", plaintext).unwrap();
            assert_eq!(ct1, ct2);
            assert_eq!(&decrypt_file(&config, &key, b"safe/item.secret", &ct1).unwrap()[..], plaintext);
            let mut corrupt = ct1.clone();
            let last = corrupt.len() - 1;
            corrupt[last] ^= 1;
            assert!(decrypt_file(&config, &key, b"safe/item.secret", &corrupt).is_err());
        }
    }

    #[test]
    fn clean_is_idempotent_and_still_refuses_foreign_records() {
        let (config, key) = fixture();
        let record = encrypt_file(&config, &key, b"a.secret", b"payload").unwrap();
        assert_eq!(clean_file(&config, &key, b"a.secret", b"payload").unwrap(), record);
        assert_eq!(clean_file(&config, &key, b"a.secret", &record).unwrap(), record);
        // The same record at another path, or tampered, is not authentic there.
        assert!(clean_file(&config, &key, b"b.secret", &record).is_err());
        let mut tampered = record.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 1;
        assert!(clean_file(&config, &key, b"a.secret", &tampered).is_err());
    }

    #[test]
    fn config_binding_and_fail_closed() {
        let (config, key) = fixture();
        let ct = encrypt_file(&config, &key, b"account.secret", b"private").unwrap();
        let mut altered = config;
        altered[7] ^= 0x40;
        assert!(decrypt_file(&altered, &key, b"account.secret", &ct).is_err());
        let mut altered_ct = ct.clone();
        altered_ct[0] = 0;
        assert!(decrypt_file(&config, &key, b"account.secret", &altered_ct).is_err());
        assert!(decrypt_file(&config, &key, b"account.secret", b"private").is_err());
    }

    #[test]
    fn ciphertext_is_bound_to_exact_git_path() {
        let (config, key) = fixture();
        let original = encrypt_file(&config, &key, b"vault/a.secret", b"identical").unwrap();
        let repeated = encrypt_file(&config, &key, b"vault/a.secret", b"identical").unwrap();
        let different = encrypt_file(&config, &key, b"vault/b.secret", b"identical").unwrap();
        assert_eq!(original, repeated, "Git determinism must be preserved within a path");
        assert_ne!(original, different, "distinct Git paths must use distinct SIV AD");
        assert_eq!(&decrypt_file(&config, &key, b"vault/a.secret", &original).unwrap()[..], b"identical");
        assert!(decrypt_file(&config, &key, b"vault/b.secret", &original).is_err());
        assert!(decrypt_file(&config, &key, b"a.secret", &original).is_err());
        assert!(decrypt_file(&config, &key, b"vault/a.secret", &different).is_err());
    }

    #[test]
    fn raw_unix_paths_are_bound_and_noncanonical_inputs_fail_closed() {
        let (config, key) = fixture();
        for path in [b"a b.secret".as_slice(), b"a'quote.secret", b"dir/new\nline.secret", b"raw/\xff.secret"] {
            let record = encrypt_file(&config, &key, path, b"payload").unwrap();
            assert_eq!(&decrypt_file(&config, &key, path, &record).unwrap()[..], b"payload");
        }
        for path in [b"".as_slice(), b".gitattributes", b"/root.secret", b"../bad.secret", b"x/../bad.secret", b"./x.secret", b"x//y.secret", b"x/./y.secret", b"x.secret/", b"evil\0.secret"] {
            assert!(validate_protected_path(path).is_err(), "accepted {:?}", path);
        }
        assert!(validate_protected_path(&std::vec![b'x'; MAX_PATH + 1]).is_err());
    }


    /// Each clause of the Lean `Realizes` contract (assumption A5) checked
    /// directly on the production `Keyed` primitive, over many lengths,
    /// paths and single-bit tamperings. Byte-exactness against an
    /// independent implementation is covered by `tests/v3_vectors.rs`.
    #[test]
    fn keyed_satisfies_the_realizes_contract() {
        let (config, key) = fixture();
        let keyed = Keyed::new(&key);
        let config: [u8; CONFIG_LEN] = config;
        // seal_config / open_config agree, and the stored tag is the seal.
        let prefix: [u8; CONFIG_PREFIX_LEN] = config[..CONFIG_PREFIX_LEN].try_into().unwrap();
        let mut tag = [0u8; TAG_LEN];
        assert!(keyed.seal_config(&prefix, &mut tag));
        assert_eq!(&tag[..], &config[CONFIG_PREFIX_LEN..]);
        assert!(keyed.open_config(&prefix, &tag));
        for bit in 0..(TAG_LEN * 8) {
            let mut bad = tag;
            bad[bit / 8] ^= 1 << (bit % 8);
            assert!(!keyed.open_config(&prefix, &bad));
        }
        // config_id is the keyless SHA-256 truncation.
        assert_eq!(keyed.config_id(&config), Sha256::digest(config)[..ID_LEN]);
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || { state ^= state << 13; state ^= state >> 7; state ^= state << 17; state };
        for len in [0usize, 1, 15, 16, 17, 255, 1000] {
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
            let flip = (next() as usize) % (sealed.len() * 8);
            let mut tampered = sealed.clone();
            tampered[flip / 8] ^= 1 << (flip % 8);
            assert!(!keyed.open_file(&config, path.as_bytes(), &tampered, &mut out));
            // Determinism: the same inputs seal to the same bytes.
            let mut again = vec![0u8; len + TAG_LEN];
            assert!(keyed.seal_file(&config, path.as_bytes(), &pt, &mut again));
            assert_eq!(again, sealed);
        }
    }
}
