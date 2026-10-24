#![no_std]
//! Pure, dependency-free Transcrypt v3 wire grammar. Crypto lives in the adapter.
//! No legacy format recognition, format guessing, or plaintext fallback.

pub const CONFIG_MAGIC: [u8; 7] = *b"TCFG3\0\x01";
pub const FILE_MAGIC: [u8; 6] = *b"TV3F\0\x01";
pub const SALT_LEN: usize = 32;
pub const TAG_LEN: usize = 16;
pub const ID_LEN: usize = 16;
pub const CONFIG_PREFIX_LEN: usize = 39;
pub const CONFIG_LEN: usize = 55;
pub const FILE_HEADER_LEN: usize = 22;
pub const FILE_MIN_LEN: usize = FILE_HEADER_LEN + TAG_LEN;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormatError {
    Length,
    Magic,
}

/// All fields in the public configuration. `tag` is authenticated by the crypto adapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    pub salt: [u8; SALT_LEN],
    pub tag: [u8; TAG_LEN],
}

pub fn encode_config_prefix(salt: &[u8; SALT_LEN]) -> [u8; CONFIG_PREFIX_LEN] {
    let mut out = [0u8; CONFIG_PREFIX_LEN];
    let mut i = 0;
    while i < CONFIG_MAGIC.len() {
        out[i] = CONFIG_MAGIC[i];
        i += 1;
    }
    let mut j = 0;
    while j < SALT_LEN {
        out[CONFIG_MAGIC.len() + j] = salt[j];
        j += 1;
    }
    out
}

pub fn encode_config(config: &Config) -> [u8; CONFIG_LEN] {
    let mut out = [0u8; CONFIG_LEN];
    let prefix = encode_config_prefix(&config.salt);
    let mut i = 0;
    while i < CONFIG_PREFIX_LEN {
        out[i] = prefix[i];
        i += 1;
    }
    let mut j = 0;
    while j < TAG_LEN {
        out[CONFIG_PREFIX_LEN + j] = config.tag[j];
        j += 1;
    }
    out
}

/// Reject unknown versions, truncated/extended metadata and malformed magic.
pub fn parse_config(input: &[u8]) -> Result<Config, FormatError> {
    if input.len() != CONFIG_LEN {
        return Err(FormatError::Length);
    }
    let mut i = 0;
    while i < CONFIG_MAGIC.len() {
        if input[i] != CONFIG_MAGIC[i] {
            return Err(FormatError::Magic);
        }
        i += 1;
    }
    let mut salt = [0u8; SALT_LEN];
    let mut j = 0;
    while j < SALT_LEN {
        salt[j] = input[CONFIG_MAGIC.len() + j];
        j += 1;
    }
    let mut tag = [0u8; TAG_LEN];
    let mut k = 0;
    while k < TAG_LEN {
        tag[k] = input[CONFIG_PREFIX_LEN + k];
        k += 1;
    }
    Ok(Config { salt, tag })
}

pub fn encode_file_header(id: &[u8; ID_LEN]) -> [u8; FILE_HEADER_LEN] {
    let mut out = [0u8; FILE_HEADER_LEN];
    let mut i = 0;
    while i < FILE_MAGIC.len() {
        out[i] = FILE_MAGIC[i];
        i += 1;
    }
    let mut j = 0;
    while j < ID_LEN {
        out[FILE_MAGIC.len() + j] = id[j];
        j += 1;
    }
    out
}

/// Parses only the public envelope header; authenticity is *not* established here.
/// Callers must authenticate the complete message before releasing plaintext.
pub fn parse_file_header(input: &[u8]) -> Result<[u8; ID_LEN], FormatError> {
    if input.len() < FILE_MIN_LEN {
        return Err(FormatError::Length);
    }
    let mut i = 0;
    while i < FILE_MAGIC.len() {
        if input[i] != FILE_MAGIC[i] {
            return Err(FormatError::Magic);
        }
        i += 1;
    }
    let mut id = [0u8; ID_LEN];
    let mut j = 0;
    while j < ID_LEN {
        id[j] = input[FILE_MAGIC.len() + j];
        j += 1;
    }
    Ok(id)
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use std::vec::Vec;
    use super::*;

    #[test]
    fn config_roundtrip_and_strict_length() {
        let config = Config { salt: [0x5a; SALT_LEN], tag: [0x81; TAG_LEN] };
        let bytes = encode_config(&config);
        assert_eq!(parse_config(&bytes), Ok(config));
        for n in 0..CONFIG_LEN {
            assert!(parse_config(&bytes[..n]).is_err());
        }
        let mut bad = bytes.to_vec();
        bad[0] = 0;
        assert_eq!(parse_config(&bad), Err(FormatError::Magic));
        bad = bytes.to_vec();
        bad.push(1);
        assert_eq!(parse_config(&bad), Err(FormatError::Length));
    }

    #[test]
    fn file_header_roundtrip_and_strict_magic() {
        let id = [0x41; ID_LEN];
        let mut record = encode_file_header(&id).to_vec();
        record.extend_from_slice(&[0x66; TAG_LEN]);
        assert_eq!(parse_file_header(&record), Ok(id));
        for n in 0..FILE_MIN_LEN {
            assert_eq!(parse_file_header(&record[..n]), Err(FormatError::Length));
        }
        record[2] = 0;
        assert_eq!(parse_file_header(&record), Err(FormatError::Magic));
    }
}
