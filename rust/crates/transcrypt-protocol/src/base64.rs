//! Strict standard-base64 decoding for transcrypt object bytes.
//!
//! The released Bash implementation stores ciphertexts as base64 text
//! (`openssl base64` / `openssl enc -a`): 64-character lines, standard
//! alphabet, `=` padding, trailing newline. Checkouts on Windows may
//! have converted line endings, so the decoder tolerates `\r` and `\n`
//! anywhere but nothing else, and is otherwise strict.

use crate::Base64Error;

const fn is_base64_char(c: u8) -> bool {
    matches!(
        c,
        b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'+' | b'/' | b'='
    )
}

const fn is_line_break(c: u8) -> bool {
    c == b'\r' || c == b'\n'
}

fn value(c: u8) -> Option<u32> {
    match c {
        b'A'..=b'Z' => Some((c - b'A') as u32),
        b'a'..=b'z' => Some((c - b'a') as u32 + 26),
        b'0'..=b'9' => Some((c - b'0') as u32 + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        b'=' => Some(64),
        _ => None,
    }
}

/// Decode standard base64 text (line breaks tolerated) to bytes.
///
/// Errors carry the byte offset at which the problem was found. The
/// output buffer is allocated once, sized at most `input.len() / 4 + 1`
/// bytes, so maliciously crafted input cannot cause unbounded allocation
/// (R-25-style boundedness).
pub fn base64_decode(input: &[u8]) -> Result<Vec<u8>, Base64Error> {
    // Pass 1: every byte must be alphabet, padding, or a line break, and
    // the number of content characters must be a multiple of four.
    let mut content = 0usize;
    for (i, &c) in input.iter().enumerate() {
        if is_line_break(c) {
            continue;
        }
        if !is_base64_char(c) {
            return Err(Base64Error::invalid_char(i, c));
        }
        content += 1;
    }
    if content % 4 != 0 {
        return Err(Base64Error::bad_length(input.len(), 0));
    }

    // Pass 2: process the content characters in four-char groups.
    let mut out = Vec::with_capacity(content / 4 * 3 + 1);
    let mut group = [0u32; 4];
    let mut group_len = 0usize;
    let mut group_start = 0usize;

    for (i, &c) in input.iter().enumerate() {
        if is_line_break(c) {
            continue;
        }
        if group_len == 0 {
            group_start = i;
        }
        group[group_len] = value(c).unwrap_or(64);
        group_len += 1;
        if group_len == 4 {
            let first_pad = group.iter().position(|&v| v == 64);
            let pad = match first_pad {
                Some(p) if group[p..].iter().all(|&v| v == 64) => 4 - p,
                Some(_) => {
                    // padding in the middle of a group (e.g. "ab=0")
                    return Err(Base64Error::padding(group_start, b'='));
                }
                None => 0,
            };
            if pad > 2 {
                return Err(Base64Error::padding(group_start, b'='));
            }
            let pad_offset = i + 1 - pad; // index of the first `=`
            match pad {
                0 => {
                    let (b0, b1, b2, b3) =
                        (group[0], group[1], group[2], group[3]);
                    out.push((b0 << 2 | b1 >> 4) as u8);
                    out.push((b1 << 4 | b2 >> 2) as u8);
                    out.push((b2 << 6 | b3) as u8);
                }
                1 => {
                    // The third symbol's two spare bits must be zero.
                    if group[2] & 0b11 != 0 {
                        return Err(Base64Error::nonzero_pad(
                            pad_offset - 1,
                            group[2] as u8,
                        ));
                    }
                    let (b0, b1, b2) = (group[0], group[1], group[2]);
                    out.push((b0 << 2 | b1 >> 4) as u8);
                    out.push((b1 << 4 | b2 >> 2) as u8);
                }
                2 => {
                    // The second symbol's four spare bits must be zero.
                    if group[1] & 0b1111 != 0 {
                        return Err(Base64Error::nonzero_pad(
                            pad_offset - 1,
                            group[1] as u8,
                        ));
                    }
                    let (b0, b1) = (group[0], group[1]);
                    out.push((b0 << 2 | b1 >> 4) as u8);
                }
                _ => unreachable!(),
            }
            group_len = 0;
        }
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 4648 test vectors.
    #[test]
    fn rfc4648_vectors() {
        let cases: &[(&str, &str)] = &[
            ("", ""),
            ("f", "Zg=="),
            ("fo", "Zm8="),
            ("foo", "Zm9v"),
            ("foob", "Zm9vYg=="),
            ("fooba", "Zm9vYmE="),
            ("foobar", "Zm9vYmFy"),
        ];
        for (plain, encoded) in cases {
            let decoded = base64_decode(encoded.as_bytes()).unwrap();
            assert_eq!(&decoded[..], plain.as_bytes(), "vector {plain}");
        }
    }

    #[test]
    fn rejects_bad_input() {
        let bad: &[&str] = &[
            "foo", // length % 4
            "fooba=", // wrong padding count for the group
            "foo===", // three pads
            "f!o", // invalid char
            "fo=oba", // padding in the middle of a group
            "ab=0", // data after padding within a group
            "====", // only padding
            "foo bar", // space is not a line break
            "fo\0o", // NUL is not a line break
        ];
        for s in bad {
            assert!(
                base64_decode(s.as_bytes()).is_err(),
                "should reject {s:?}"
            );
        }
    }

    #[test]
    fn tolerates_line_breaks_and_crlf() {
        let long = "Zm9vYmFy".repeat(10); // encodes "foobar" x 10
        let decoded_expect = b"foobar".repeat(10);
        let mut ossl = String::new();
        for chunk in long.as_bytes().chunks(64) {
            ossl.push_str(
                std::str::from_utf8(chunk).expect("utf8"),
            );
            ossl.push('\n');
        }
        assert_eq!(
            base64_decode(ossl.as_bytes()).unwrap(),
            decoded_expect
        );
        let crlf = ossl.replace('\n', "\r\n");
        assert_eq!(
            base64_decode(crlf.as_bytes()).unwrap(),
            decoded_expect
        );
    }

    #[test]
    fn padded_groups_decode() {
        assert_eq!(base64_decode(b"Zg==").unwrap(), b"f");
        assert_eq!(base64_decode(b"Zm8=").unwrap(), b"fo");
        assert_eq!(base64_decode(b"Zm9v").unwrap(), b"foo");
        // two adjacent complete groups
        assert_eq!(
            base64_decode(b"QUJDQUJD").unwrap(),
            b"ABCABC"
        );
    }

    #[test]
    fn nonzero_residual_bits_rejected() {
        // one pad: the third symbol's spare 2 bits must be zero.
        // '8' = 111100 (spare 00) is fine; '9' = 100001 (spare 01) is not.
        assert_eq!(base64_decode(b"Zm8=").unwrap(), b"fo");
        assert!(base64_decode(b"Zm9=").is_err());
        // two pads: the second symbol's spare 4 bits must be zero.
        // 'g' = 100000 (spare 0000) is fine; '0' = 110100 (spare 0100) is not.
        assert_eq!(base64_decode(b"Zg==").unwrap(), b"f");
        assert!(base64_decode(b"Z0==").is_err());
    }
}
