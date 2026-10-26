//! Small, total bit-manipulation core shared by the Base64 encoder/decoder.
//!
//! The corresponding fixed-width algebra is checked independently by
//! `proofs/smt/base64_bitvector.c`. That check models these exact bit
//! expressions; it does not yet constitute an Aeneas proof of the Rust code.

/// Convert exactly three input bytes into four six-bit values.
/// The result is in the range 0..64 for every possible input byte.
#[inline]
pub(crate) fn split_triple(a: u8, b: u8, c: u8) -> [u8; 4] {
    [
        a >> 2,
        ((a & 3) << 4) | (b >> 4),
        ((b & 15) << 2) | (c >> 6),
        c & 63,
    ]
}

/// Convert four six-bit values back into three bytes.
/// Callers validate the Base64 alphabet and padding before using the result.
#[inline]
pub(crate) fn join_quartet(s: [u8; 4]) -> [u8; 3] {
    [
        (s[0] << 2) | (s[1] >> 4),
        (s[1] << 4) | (s[2] >> 2),
        (s[2] << 6) | s[3],
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_and_two_byte_tails_are_canonical() {
        for a in 0..=255u8 {
            let symbols = split_triple(a, 0, 0);
            assert_eq!(symbols[1] & 15, 0);
            assert_eq!(join_quartet(symbols)[0], a);
        }
        for a in 0..=255u8 {
            for b in 0..=255u8 {
                let symbols = split_triple(a, b, 0);
                assert_eq!(symbols[2] & 3, 0);
                assert_eq!(&join_quartet(symbols)[..2], &[a, b]);
            }
        }
    }

    #[test]
    fn full_blocks_roundtrip() {
        let mut x = 0x1234_5678u32;
        for _ in 0..100_000 {
            x = x.wrapping_mul(1664525).wrapping_add(1013904223);
            let a = (x >> 16) as u8;
            let b = (x >> 8) as u8;
            let c = x as u8;
            assert_eq!(join_quartet(split_triple(a, b, c)), [a, b, c]);
        }
    }
}
