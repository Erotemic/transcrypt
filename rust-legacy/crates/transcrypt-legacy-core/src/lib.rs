//! Small pure compatibility functions. These are Aeneas candidates; OpenSSL,
//! Git, processes, and credential storage are deliberately outside this module.
//!
//! This precisely specifies *legacy v2* behavior, not a secure v3 format.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
use alloc::string::String;
use alloc::vec::Vec;

/// Legacy OpenSSL CLI HMAC key bytes: verbatim Git path, colon, password.
/// The password need not be UTF-8. Empty paths are rejected by the caller.
///
/// WARNING: the password is an input to both the HMAC and OpenSSL's legacy
/// EVP_BytesToKey(MD5). Do not reuse this construction in the modern format.
pub fn legacy_hmac_key(path: &[u8], password: &[u8]) -> Vec<u8> {
    let mut key = Vec::with_capacity(path.len().saturating_add(password.len()).saturating_add(1));
    key.extend_from_slice(path);
    key.push(b':');
    key.extend_from_slice(password);
    key
}

/// Deterministic legacy salt = last eight bytes of HMAC-SHA256 digest.
pub fn legacy_salt_from_digest(digest: &[u8; 32]) -> [u8; 8] {
    let mut out = [0u8; 8];
    out.copy_from_slice(&digest[24..32]);
    out
}

/// In the shipped Bash v2 filter, these initial ASCII bytes signal a stored
/// blob, *without authentication or even parsing*. Preserve that behavior
/// only for existing legacy records, and document it as a security defect.
pub fn legacy_looks_encrypted(input: &[u8]) -> bool {
    input.starts_with(b"U2FsdGVk")
}

/// A distinct future protocol discriminator must not be processed using the
/// legacy crypto configuration. This recognizes only the provisional format
/// from prior work; it makes no claim that the future wire format is frozen.
pub fn prohibited_provisional_v3(input: &[u8]) -> bool {
    input.starts_with(b"TCRYPT3:")
}

/// Context names match the Bash project's `CONTEXT_REGEX` exactly:
/// `[a-z](-?[a-z0-9])*`. The literal `default` is the implicit context.
pub fn valid_context_name(bytes: &[u8]) -> bool {
    if bytes.is_empty() || !bytes[0].is_ascii_lowercase() {
        return false;
    }
    let mut prev_dash = false;
    for &c in &bytes[1..] {
        if c == b'-' {
            if prev_dash {
                return false;
            }
            prev_dash = true;
        } else if c.is_ascii_lowercase() || c.is_ascii_digit() {
            prev_dash = false;
        } else {
            return false;
        }
    }
    !prev_dash
}

/// Decode one hexadecimal digit without using a locale or Unicode conversion.
pub fn hex_value(d: u8) -> Option<u8> {
    match d {
        b'0'..=b'9' => Some(d - b'0'),
        b'a'..=b'f' => Some(d - b'a' + 10),
        b'A'..=b'F' => Some(d - b'A' + 10),
        _ => None,
    }
}

/// Parse exactly 64 ASCII hex digits into the 32-byte OpenSSL HMAC digest.
pub fn parse_sha256_hex(hex: &[u8]) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut digest = [0u8; 32];
    for i in 0..32 {
        let high = hex_value(hex[2 * i])?;
        let low = hex_value(hex[2 * i + 1])?;
        digest[i] = (high << 4) | low;
    }
    Some(digest)
}

pub fn salt_hex(salt: &[u8; 8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(16);
    for &b in salt {
        result.push(HEX[(b >> 4) as usize] as char);
        result.push(HEX[(b & 15) as usize] as char);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_is_last_eight_bytes_not_first() {
        let mut digest = [0u8; 32];
        for (i, b) in digest.iter_mut().enumerate() { *b = i as u8; }
        assert_eq!(legacy_salt_from_digest(&digest), [24, 25, 26, 27, 28, 29, 30, 31]);
        assert_eq!(salt_hex(&legacy_salt_from_digest(&digest)), "18191a1b1c1d1e1f");
    }

    #[test]
    fn legacy_key_bytes_are_exact() {
        assert_eq!(legacy_hmac_key(b"folder/a b", b"secret").as_slice(), b"folder/a b:secret");
        assert_eq!(legacy_hmac_key(b"a\nb", b"p\xff").as_slice(), b"a\nb:p\xff");
    }

    #[test]
    fn context_grammar_matches_bash() {
        for valid in ["default", "ab", "a1", "a-1", "a-b-c", "a1b", "a-b1"] {
            assert!(valid_context_name(valid.as_bytes()), "valid: {valid}");
        }
        for invalid in ["", "A", "1a", "a-", "-a", "a--b", "a_B", "a.b", "a/B"] {
            assert!(!valid_context_name(invalid.as_bytes()), "invalid: {invalid}");
        }
    }

    #[test]
    fn strict_digest_bytes() {
        let hex = b"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
        let out = parse_sha256_hex(hex).unwrap();
        assert_eq!(out[0], 0);
        assert_eq!(out[31], 31);
        assert!(parse_sha256_hex(&hex[..63]).is_none());
        assert!(parse_sha256_hex(&[b'z'; 64]).is_none());
    }
}
