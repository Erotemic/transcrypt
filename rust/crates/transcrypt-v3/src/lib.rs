//! Exact v3 cryptographic operations: Argon2id and deterministic AES-256-CMAC-SIV.
//! Assumes RustCrypto primitive correctness; protocol parsing lives in `transcrypt-v3-core`.
//! This is a research prototype, not an audited security release.

use aes_siv::{siv::Aes256Siv, KeyInit};
use argon2::{Algorithm, Argon2, Params, Version};
use sha2::{Digest, Sha256};
use subtle::ConstantTimeEq;
use transcrypt_v3_core::{
    encode_config, encode_config_prefix, encode_file_header, parse_config, parse_file_header,
    Config, CONFIG_LEN, FILE_HEADER_LEN, FILE_MIN_LEN, ID_LEN, SALT_LEN, TAG_LEN,
};
use zeroize::Zeroizing;

pub const MAX_FILE: usize = 16 * 1024 * 1024;
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

fn siv(key: &[u8; KEY_SIZE]) -> Result<Aes256Siv, String> {
    Aes256Siv::new_from_slice(key).map_err(|_| "AES-SIV key rejected".into())
}

fn config_verifier(key: &[u8; KEY_SIZE], salt: &[u8; SALT_LEN]) -> Result<[u8; TAG_LEN], String> {
    let prefix = encode_config_prefix(salt);
    let headers: [&[u8]; 2] = [CONFIG_DOMAIN, &prefix];
    let ciphertext = siv(key)?.encrypt(headers, &[])
        .map_err(|_| "cannot compute configuration authenticator")?;
    ciphertext.try_into().map_err(|_| "wrong AES-SIV tag size".into())
}

pub fn initialize_config(password: &[u8], salt: &[u8; SALT_LEN])
    -> Result<([u8; CONFIG_LEN], SecretKey), String>
{
    let key = derive_key(password, salt)?;
    let tag = config_verifier(&key, salt)?;
    Ok((encode_config(&Config { salt: *salt, tag }), key))
}

pub fn authenticate_config(config_bytes: &[u8], key: &[u8; KEY_SIZE]) -> Result<(), String> {
    let config = parse_config(config_bytes).map_err(|_| "invalid public v3 configuration")?;
    let expect = config_verifier(key, &config.salt)?;
    if !bool::from(expect.ct_eq(&config.tag)) {
        return Err("incorrect credentials or tampered public v3 configuration".into());
    }
    Ok(())
}

pub fn unlock_config(password: &[u8], config_bytes: &[u8]) -> Result<SecretKey, String> {
    let config = parse_config(config_bytes).map_err(|_| "invalid public v3 configuration")?;
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

pub fn encrypt_file(config_bytes: &[u8], key: &[u8; KEY_SIZE], plaintext: &[u8])
    -> Result<Vec<u8>, String>
{
    if plaintext.len() > MAX_FILE {
        return Err("input exceeds 16 MiB limit".into());
    }
    authenticate_config(config_bytes, key)?;
    let headers: [&[u8]; 2] = [FILE_DOMAIN, config_bytes];
    let encrypted = siv(key)?.encrypt(headers, plaintext)
        .map_err(|_| "AES-SIV encryption failed")?;
    let mut out = Vec::with_capacity(FILE_HEADER_LEN + encrypted.len());
    out.extend_from_slice(&encode_file_header(&config_id(config_bytes)));
    out.extend_from_slice(&encrypted);
    Ok(out)
}

pub fn decrypt_file(config_bytes: &[u8], key: &[u8; KEY_SIZE], record: &[u8])
    -> Result<Vec<u8>, String>
{
    if record.len() > MAX_FILE + FILE_MIN_LEN {
        return Err("ciphertext exceeds 16 MiB limit".into());
    }
    authenticate_config(config_bytes, key)?;
    let record_id = parse_file_header(record).map_err(|_| "invalid v3 ciphertext envelope")?;
    if !bool::from(record_id.ct_eq(&config_id(config_bytes))) {
        return Err("v3 ciphertext belongs to different public configuration".into());
    }
    let headers: [&[u8]; 2] = [FILE_DOMAIN, config_bytes];
    let plaintext = siv(key)?.decrypt(headers, &record[FILE_HEADER_LEN..])
        .map_err(|_| "v3 ciphertext authentication failed")?;
    if plaintext.len() > MAX_FILE {
        return Err("decrypted data exceeds 16 MiB limit".into());
    }
    Ok(plaintext)
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
            let ct1 = encrypt_file(&config, &key, plaintext).unwrap();
            let ct2 = encrypt_file(&config, &key, plaintext).unwrap();
            assert_eq!(ct1, ct2);
            assert_eq!(decrypt_file(&config, &key, &ct1).unwrap(), plaintext);
            let mut corrupt = ct1.clone();
            let last = corrupt.len() - 1;
            corrupt[last] ^= 1;
            assert!(decrypt_file(&config, &key, &corrupt).is_err());
        }
    }

    #[test]
    fn config_binding_and_fail_closed() {
        let (config, key) = fixture();
        let ct = encrypt_file(&config, &key, b"private").unwrap();
        let mut altered = config;
        altered[7] ^= 0x40;
        assert!(decrypt_file(&altered, &key, &ct).is_err());
        let mut altered_ct = ct.clone();
        altered_ct[0] = 0;
        assert!(decrypt_file(&config, &key, &altered_ct).is_err());
        assert!(decrypt_file(&config, &key, b"private").is_err());
    }
}
