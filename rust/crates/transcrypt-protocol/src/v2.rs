//! Detection and structural parsing of the released legacy (v2) format.
//!
//! The v2 wire object is base64 text of a binary blob
//! `"Salted__" || salt[8] || AES-CBC ciphertext (PKCS7)`. This module
//! classifies input and splits that structure; it does not derive keys
//! or verify the ciphertext (those require the password and belong to
//! the future crypto adapter).
//!
//! The grammar below is derived from the released Bash implementation
//! (see `docs/verification/reference/` and the implementation-progress
//! log), not from an approved specification.
//!
//! Discriminator semantics (R-03: exactly one decoder, no fallback):
//! input that *starts* like a v2 object but fails structural validation
//! is reported as `Format::Invalid`, never silently demoted to
//! plaintext.

use crate::base64::base64_decode;
use crate::Base64Error;

/// Structured errors from [`parse_v2`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum V2Error {
    /// The input does not start with the v2 base64 prefix.
    NotV2,
    /// The base64 text is malformed.
    Base64(Base64Error),
    /// Decoded bytes do not start with the `Salted__` binary header.
    BadBinaryMagic,
    /// The ciphertext portion is empty or not a whole number of AES
    /// blocks.
    BadCiphertextLength { decoded_len: usize },
}

/// The base64 prefix of the binary `Salted__` header — the only magic
/// the Bash implementation checks (`U2FsdGVk`).
pub const V2_BASE64_PREFIX: &[u8; 8] = b"U2FsdGVk";

/// The binary salt header, first 8 bytes of a decoded v2 blob.
pub const V2_BINARY_MAGIC: &[u8; 8] = b"Salted__";

/// Header size of a decoded v2 blob: `Salted__` (8) + salt (8).
pub const V2_HEADER_LEN: usize = 16;

/// Size of the derived salt in a decoded v2 blob.
pub const V2_SALT_LEN: usize = 8;

/// One AES-CBC block.
const AES_BLOCK: usize = 16;

/// A classification of an object's leading bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    /// No v2 magic. Includes empty input: the Bash filter passes empty
    /// files through unencrypted, so this is a defined legacy
    /// representation, not an error.
    Plaintext,
    /// A structurally complete legacy v2 object.
    V2,
    /// Starts with the v2 base64 prefix but fails structural
    /// validation (corrupt or hostile). Must fail closed: never
    /// reclassified as plaintext.
    Invalid,
}

/// A structurally valid v2 object, split into its fields.
///
/// Owns the decoded bytes (one allocation); no decryption is
/// performed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V2Record {
    /// The 8-byte derived salt (last 8 bytes of the file's
    /// HMAC-SHA256 in the Bash implementation).
    pub salt: [u8; 8],
    /// The AES-CBC ciphertext (PKCS7-padded, whole blocks).
    pub ciphertext: Vec<u8>,
}

/// Check the cheap prefix test (the Bash implementation's
/// first-bytes check) without decoding.
pub fn is_v2_prefix(bytes: &[u8]) -> bool {
    bytes.len() >= V2_BASE64_PREFIX.len()
        && &bytes[..V2_BASE64_PREFIX.len()] == V2_BASE64_PREFIX
}

/// Parse a v2 object. Fails closed on any structural problem.
pub fn parse_v2(input: &[u8]) -> Result<V2Record, V2Error> {
    if !is_v2_prefix(input) {
        return Err(V2Error::NotV2);
    }
    let decoded = base64_decode(input).map_err(V2Error::Base64)?;
    if decoded.len() < V2_HEADER_LEN
        || &decoded[..V2_BINARY_MAGIC.len()] != V2_BINARY_MAGIC
    {
        return Err(V2Error::BadBinaryMagic);
    }
    let ciphertext_len = decoded.len() - V2_HEADER_LEN;
    if ciphertext_len < AES_BLOCK || ciphertext_len % AES_BLOCK != 0 {
        return Err(V2Error::BadCiphertextLength {
            decoded_len: decoded.len(),
        });
    }
    let salt: [u8; 8] = decoded[V2_BINARY_MAGIC.len()..V2_BINARY_MAGIC.len() + V2_SALT_LEN]
        .try_into()
        .unwrap();
    let ciphertext = decoded[V2_HEADER_LEN..].to_vec();
    Ok(V2Record { salt, ciphertext })
}

/// Classify an object without a full parse.
///
/// Cheap enough to run on every filter invocation (mirrors the Bash
/// implementation's first-bytes check).
pub fn detect_format(input: &[u8]) -> Format {
    if !is_v2_prefix(input) {
        return Format::Plaintext;
    }
    match parse_v2(input) {
        Ok(_) => Format::V2,
        Err(V2Error::NotV2) => unreachable!(),
        Err(_) => Format::Invalid,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base64;

    /// Wrap binary bytes as 64-character base64 lines (the way
    /// `openssl base64` does), using a tiny local encoder.
    fn wrap_b64(data: &[u8]) -> Vec<u8> {
        const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut s = String::new();
        for chunk in data.chunks(3) {
            let b0 = chunk[0] as u32;
            let b1 = *chunk.get(1).unwrap_or(&0) as u32;
            let b2 = *chunk.get(2).unwrap_or(&0) as u32;
            let n = (b0 << 16) | (b1 << 8) | b2;
            s.push(A[(n >> 18) as usize & 63] as char);
            s.push(A[(n >> 12) as usize & 63] as char);
            if chunk.len() > 1 {
                s.push(A[(n >> 6) as usize & 63] as char);
            } else {
                s.push('=');
            }
            if chunk.len() > 2 {
                s.push(A[n as usize & 63] as char);
            } else {
                s.push('=');
            }
        }
        let mut out = String::new();
        for chunk in s.as_bytes().chunks(64) {
            out.push_str(std::str::from_utf8(chunk).unwrap());
            out.push('\n');
        }
        out.into_bytes()
    }

    fn blob(salt: &[u8; 8], ciphertext_len: usize) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(V2_BINARY_MAGIC);
        v.extend_from_slice(salt);
        v.extend(std::iter::repeat(0x42u8).take(ciphertext_len));
        v
    }

    #[test]
    fn parses_well_formed_blob() {
        let salt = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let text = wrap_b64(&blob(&salt, 48));
        let rec = parse_v2(&text).unwrap();
        assert_eq!(rec.salt, salt);
        assert_eq!(rec.ciphertext.len(), 48);
        assert_eq!(detect_format(&text), Format::V2);
    }

    #[test]
    fn rejects_short_ciphertext() {
        let salt = [0u8; 8];
        // header only, no ciphertext
        let text = wrap_b64(&blob(&salt, 0));
        assert!(matches!(
            parse_v2(&text),
            Err(V2Error::BadCiphertextLength {
                decoded_len: 16
            })
        ));
        assert_eq!(detect_format(&text), Format::Invalid);
        // 15-byte ciphertext is not block-aligned
        let text = wrap_b64(&blob(&salt, 15));
        assert!(matches!(
            parse_v2(&text),
            Err(V2Error::BadCiphertextLength { .. })
        ));
        assert_eq!(detect_format(&text), Format::Invalid);
    }

    #[test]
    fn rejects_bad_binary_magic() {
        // Text begins with the v2 base64 prefix ("U2FsdGVk"), but the
        // decoded binary does not start with "Salted__": the 7th-8th
        // bytes are "XX" instead of "__".
        let mut v = b"SaltedXX".to_vec();
        v.extend_from_slice(&[0u8; 8]);
        v.extend_from_slice(&[0u8; 16]);
        let text = wrap_b64(&v);
        assert!(
            text.starts_with(b"U2FsdGVk"),
            "test precondition: text has the v2 prefix"
        );
        assert_eq!(
            detect_format(&text),
            Format::Invalid,
            "corrupt magic must not fall through to plaintext"
        );
        assert!(matches!(
            parse_v2(&text),
            Err(V2Error::BadBinaryMagic)
        ));
    }

    #[test]
    fn rejects_malformed_base64() {
        let mut text = b"U2FsdGVk".to_vec();
        text.extend_from_slice(b"!!!\n");
        assert!(parse_v2(&text).is_err());
        assert_eq!(detect_format(&text), Format::Invalid);
    }

    #[test]
    fn plaintext_classification() {
        assert_eq!(detect_format(b""), Format::Plaintext);
        assert_eq!(
            detect_format(b"just some text\n"),
            Format::Plaintext
        );
        // base64-looking but without the magic
        assert_eq!(detect_format(b"Zm9vYmFy\n"), Format::Plaintext);
        // prefix too short
        assert_eq!(detect_format(b"U2FsdG"), Format::Plaintext);
    }

    #[test]
    fn empty_input_is_plaintext_not_invalid() {
        assert_eq!(detect_format(b""), Format::Plaintext);
        assert!(matches!(parse_v2(b""), Err(V2Error::NotV2)));
    }

    // Hostile inputs: must classify without panicking.
    #[test]
    fn hostile_inputs() {
        let cases: Vec<Vec<u8>> = vec![
            vec![0u8; 1 << 20], // all NULs
            vec![0xff; 1 << 20], // all 0xff
            b"U2FsdGVk".repeat(100_000).to_vec(), // repeated prefix
            {
                // prefix then 1MB of LCG-generated data
                let mut v = b"U2FsdGVk".to_vec();
                let mut x = 0x12345678u32;
                for _ in 0..(1 << 20) {
                    x = x
                        .wrapping_mul(1664525)
                        .wrapping_add(1013904223);
                    v.push((x >> 24) as u8);
                }
                v
            },
            // prefix then valid base64 that decodes to the wrong binary
            {
                let mut v = b"U2FsdGVk".to_vec();
                v.extend_from_slice(b"QUFBQUFBQUFB\n");
                v
            },
        ];
        for c in &cases {
            let _ = detect_format(c); // must not panic
            let _ = parse_v2(c);
        }
    }

    // Round-trip the decoder against its own encoder for random data.
    #[test]
    fn decoder_encoder_agreement() {
        let mut x = 0xDEADBEEFu32;
        let mut data = Vec::new();
        for _ in 0..1000 {
            x = x
                .wrapping_mul(1664525)
                .wrapping_add(1013904223);
            data.push((x >> 24) as u8);
        }
        let text = wrap_b64(&data);
        assert_eq!(base64::base64_decode(&text).unwrap(), data);
    }
}
