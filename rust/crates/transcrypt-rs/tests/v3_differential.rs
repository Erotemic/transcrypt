//! Differential tests of the production primitive (`Keyed`, RustCrypto
//! AES-SIV and Argon2id) against independent implementations: OpenSSL
//! AES-SIV and reference Argon2id, via `tests/v3/reference/differential.py`.
//! No Python is needed to run these Rust tests.
use transcrypt_rs::{authenticate_config, clean_file, decrypt_file, derive_key, encrypt_file, Keyed};
use transcrypt_v3_core::{V3Primitives, CONFIG_LEN, CONFIG_PREFIX_LEN, FILE_HEADER_LEN, TAG_LEN};

mod common;
use common::hex;

struct Case { name: String, key: [u8; 64], config: Vec<u8>, path: Vec<u8>, plaintext: Vec<u8>, record: Vec<u8> }

fn cases() -> Vec<Case> {
    include_str!("../../../../tests/v3/reference/differential.tsv").lines().map(|line| {
        let c: Vec<&str> = line.split('\t').collect();
        assert_eq!(c.len(), 6);
        Case {
            name: c[0].into(), key: hex(c[1]).try_into().unwrap(), config: hex(c[2]),
            path: hex(c[3]), plaintext: hex(c[4]), record: hex(c[5]),
        }
    }).collect()
}

/// Bit positions to flip: every bit of short records, otherwise every bit
/// of the header and tag plus a spread over the body.
fn flips(len: usize) -> Vec<usize> {
    if len <= 80 { return (0..len * 8).collect(); }
    let mut bits: Vec<usize> = (0..(FILE_HEADER_LEN + TAG_LEN) * 8).collect();
    bits.extend((0..256).map(|i| (FILE_HEADER_LEN + TAG_LEN) * 8 + i * (len - FILE_HEADER_LEN - TAG_LEN) * 8 / 256));
    bits
}

#[test]
fn keyed_matches_openssl_aes_siv_byte_for_byte() {
    let all = cases();
    assert!(all.len() >= 20);
    for (i, case) in all.iter().enumerate() {
        let n = &case.name;
        let config: [u8; CONFIG_LEN] = case.config.clone().try_into().unwrap();
        let keyed = Keyed::new(&case.key);
        let prefix: [u8; CONFIG_PREFIX_LEN] = config[..CONFIG_PREFIX_LEN].try_into().unwrap();
        let mut tag = [0u8; TAG_LEN];
        assert!(keyed.seal_config(&prefix, &mut tag), "{n}");
        assert_eq!(&tag[..], &config[CONFIG_PREFIX_LEN..], "{n}: config tag");
        authenticate_config(&config, &case.key).unwrap();
        // Sealing and opening, through the verified core.
        assert_eq!(encrypt_file(&config, &case.key, &case.path, &case.plaintext).unwrap(), case.record, "{n}");
        assert_eq!(&decrypt_file(&config, &case.key, &case.path, &case.record).unwrap()[..], &case.plaintext[..], "{n}");
        assert_eq!(clean_file(&config, &case.key, &case.path, &case.record).unwrap(), case.record, "{n}");
        // The primitive alone, on exactly the SIV part of the record.
        let sealed = &case.record[FILE_HEADER_LEN..];
        let mut out = vec![0u8; sealed.len()];
        assert!(keyed.seal_file(&config, &case.path, &case.plaintext, &mut out));
        assert_eq!(out, sealed, "{n}");
        // Every tampering fails.
        for bit in flips(case.record.len()) {
            let mut bad = case.record.clone();
            bad[bit / 8] ^= 1 << (bit % 8);
            assert!(decrypt_file(&config, &case.key, &case.path, &bad).is_err(), "{n}: bit {bit}");
        }
        for cut in [1, TAG_LEN, case.record.len() - FILE_HEADER_LEN] {
            if cut <= case.record.len() {
                let short = &case.record[..case.record.len() - cut];
                assert!(decrypt_file(&config, &case.key, &case.path, short).is_err(), "{n}: truncated by {cut}");
            }
        }
        for extra in [&[0u8][..], &[0u8; 16], &case.record[FILE_HEADER_LEN..FILE_HEADER_LEN + TAG_LEN]] {
            let long = [&case.record[..], extra].concat();
            assert!(decrypt_file(&config, &case.key, &case.path, &long).is_err(), "{n}: extended");
        }
        // Wrong path, prefix/suffix path, other configuration, other key.
        for path in [[&case.path[..], b"x"].concat(), case.path[1..].to_vec(), b"other.secret".to_vec()] {
            assert!(decrypt_file(&config, &case.key, &path, &case.record).is_err(), "{n}: path");
        }
        let other = &all[(i + 1) % all.len()];
        assert!(decrypt_file(&other.config, &other.key, &case.path, &case.record).is_err(), "{n}: other repo");
        assert!(authenticate_config(&config, &other.key).is_err(), "{n}: other key");
        let mut short_out = vec![0u8; case.plaintext.len() + 1];
        assert!(!keyed.open_file(&config, &case.path, sealed, &mut short_out), "{n}: wrong size");
    }
}

#[test]
fn argon2id_matches_the_reference_implementation() {
    for line in include_str!("../../../../tests/v3/reference/kdf.tsv").lines() {
        let c: Vec<&str> = line.split('\t').collect();
        let salt: [u8; 32] = hex(c[2]).try_into().unwrap();
        assert_eq!(&derive_key(&hex(c[1]), &salt).unwrap()[..], &hex(c[3])[..], "{}", c[0]);
    }
}

#[test]
fn size_bounds_are_exact_at_every_layer() {
    use transcrypt_rs::{MAX_FILE, MAX_RECORD};
    let case = &cases()[0];
    let config = &case.config;
    let path = b"big.secret";
    // The largest plaintext seals and opens; one more byte is refused.
    let max = vec![0x5au8; MAX_FILE];
    let record = encrypt_file(config, &case.key, path, &max).unwrap();
    assert_eq!(record.len(), MAX_RECORD);
    assert_eq!(&decrypt_file(config, &case.key, path, &record).unwrap()[..], &max[..]);
    assert!(encrypt_file(config, &case.key, path, &vec![0u8; MAX_FILE + 1]).is_err());
    let mut long = record.clone();
    long.push(0);
    assert!(decrypt_file(config, &case.key, path, &long).is_err());
    // Every record shorter than header + tag is refused, including empty.
    for len in 0..(FILE_HEADER_LEN + TAG_LEN) {
        assert!(decrypt_file(config, &case.key, path, &case.record[..len.min(case.record.len())]).is_err(), "{len}");
    }
    // A header-only record with a forged all-zero tag is refused.
    let mut forged = case.record[..FILE_HEADER_LEN].to_vec();
    forged.extend_from_slice(&[0u8; TAG_LEN]);
    assert!(decrypt_file(config, &case.key, path, &forged).is_err());
}

/// Randomized mutation testing (deterministic seed): inserting, deleting,
/// replacing or swapping bytes anywhere in a genuine record never yields an
/// accepted record, and random bodies behind a genuine header never open.
#[test]
fn random_mutations_never_authenticate() {
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || { state ^= state << 13; state ^= state >> 7; state ^= state << 17; state };
    for case in cases().iter().filter(|c| c.record.len() < 400) {
        let (config, key, path) = (&case.config, &case.key, &case.path);
        for _ in 0..300 {
            let mut bad = case.record.clone();
            for _ in 0..(1 + next() % 3) {
                let at = (next() as usize) % (bad.len() + 1);
                match next() % 4 {
                    0 => bad.insert(at, next() as u8),
                    1 if !bad.is_empty() => { bad.remove(at.min(bad.len() - 1)); },
                    2 if at < bad.len() => bad[at] ^= 1 + (next() % 255) as u8,
                    _ if bad.len() > 1 => { let (n, j) = (bad.len(), next() as usize); bad.swap(at.min(n - 1), j % n); },
                    _ => {},
                }
            }
            if bad != case.record {
                assert!(decrypt_file(config, key, path, &bad).is_err(), "{}: accepted a mutation", case.name);
            }
            let mut random = case.record[..FILE_HEADER_LEN].to_vec();
            random.extend((0..(TAG_LEN + (next() % 64) as usize)).map(|_| next() as u8));
            assert!(decrypt_file(config, key, path, &random).is_err(), "{}: accepted random body", case.name);
        }
    }
}
