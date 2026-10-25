//! Exact v3 cryptographic primitives: Argon2id and deterministic AES-256-CMAC-SIV.
//!
//! This crate only *implements* the `V3Primitives` trait of
//! `transcrypt-v3-core` and derives keys. Every protocol decision (path policy,
//! configuration authentication, envelope, configuration binding, release of
//! plaintext) is made by the Aeneas-extracted core functions it calls.
//! Assumes RustCrypto primitive correctness. Research prototype, not audited.

use aes_siv::{siv::Aes256Siv, KeyInit};
use argon2::{Algorithm, Argon2, Params, Version};
use sha2::{Digest, Sha256};
pub use transcrypt_v3_core::{MAX_FILE, MAX_PATH, MAX_RECORD};
use transcrypt_v3_core::{
    Refusal, V3Primitives, CONFIG_LEN, CONFIG_PREFIX_LEN, FILE_MIN_LEN, ID_LEN, SALT_LEN, TAG_LEN,
};
use zeroize::Zeroizing;

/// A canonical Git-relative name is part of the authenticated cryptographic
/// context. The policy itself is `transcrypt_v3_core::is_canonical_protected_path`.
pub fn validate_protected_path(path: &[u8]) -> Result<(), String> {
    if transcrypt_v3_core::is_canonical_protected_path(path) {
        Ok(())
    } else {
        Err("v3 requires a canonical Git-relative *.secret path".into())
    }
}
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
    let kdf = Argon2::new(Algorithm::Argon2id, Version::V0x13, params);
    let mut key = Zeroizing::new([0u8; KEY_SIZE]);
    kdf.hash_password_into(password, salt, &mut key[..])
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

    fn seal_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], plaintext: &[u8], out: &mut [u8]) -> bool {
        let headers: [&[u8]; 3] = [FILE_DOMAIN, config, path];
        match self.siv().map(|mut siv| siv.encrypt(headers, plaintext)) {
            Some(Ok(sealed)) if sealed.len() == out.len() => {
                out.copy_from_slice(&sealed);
                true
            }
            _ => false,
        }
    }

    fn open_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], sealed: &[u8], out: &mut [u8]) -> bool {
        let headers: [&[u8]; 3] = [FILE_DOMAIN, config, path];
        match self.siv().map(|mut siv| siv.decrypt(headers, sealed)) {
            Some(Ok(plaintext)) => {
                let plaintext = Zeroizing::new(plaintext);
                if plaintext.len() != out.len() {
                    return false;
                }
                out.copy_from_slice(&plaintext);
                true
            }
            _ => false,
        }
    }

    fn config_id(&self, config: &[u8; CONFIG_LEN]) -> [u8; ID_LEN] {
        config_id(config)
    }
}

fn refusal(r: Refusal) -> String {
    match r {
        Refusal::Path => "v3 requires a canonical Git-relative *.secret path",
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
    }
    .into()
}

/// Exact fixed-length view of a public configuration.
pub fn config_array(config_bytes: &[u8]) -> Result<&[u8; CONFIG_LEN], String> {
    config_bytes.try_into().map_err(|_| "invalid public v3 configuration".into())
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
    let config = transcrypt_v3_core::parse_config(config_bytes)
        .map_err(|_| "invalid public v3 configuration")?;
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
        for path in [b"".as_slice(), b"absolute", b"/root.secret", b"../bad.secret", b"x/../bad.secret", b"./x.secret", b"x//y.secret", b"x/./y.secret", b"x.secret/", b"evil\0.secret"] {
            assert!(validate_protected_path(path).is_err(), "accepted {:?}", path);
        }
        assert!(validate_protected_path(&std::vec![b'x'; MAX_PATH + 1]).is_err());
    }

}
