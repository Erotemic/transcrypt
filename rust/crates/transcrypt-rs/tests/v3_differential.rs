//! Differential tests of the production primitive (`Keyed`, RustCrypto
//! AES-SIV and Argon2id) against independent implementations: OpenSSL
//! AES-SIV and reference Argon2id, via `tests/v3/reference/differential.py`.
//! No Python is needed to run these Rust tests.
use transcrypt_rs::{authenticate_config, clean_file, decrypt_file, derive_key, encrypt_file, Keyed, KEY_SIZE};
use transcrypt_v3_core::{V3Primitives, CONFIG_LEN, CONFIG_PREFIX_LEN, FILE_HEADER_LEN, FILE_MIN_LEN, SALT_LEN, TAG_LEN};

mod common;
use common::hex;

const BITS: usize = u8::BITS as usize;
/// Records up to this long have every bit flipped.
const SHORT_RECORD: usize = 80;
/// The number of body bits flipped in a longer record, spread evenly.
const BODY_FLIPS: usize = 256;
/// The fewest differential cases the fixture must hold.
const MIN_CASES: usize = 20;
/// Marsaglia's xorshift64 (shifts 13, 7, 17) from a fixed seed.
const SEED: u64 = 0x2545_f491_4f6c_dd1d;
const SHIFTS: (u32, u32, u32) = (13, 7, 17);
/// Mutation testing: records shorter than this, so many rounds each, of at
/// most so many mutations.
const MUTATED_RECORD_LIMIT: usize = 400;
const MUTATION_ROUNDS: usize = 300;
const MAX_MUTATIONS: u64 = 3;
/// The most random bytes put behind a genuine header beyond a tag's worth.
const MAX_RANDOM_EXTRA: u64 = 64;

struct Case { name: String, key: [u8; KEY_SIZE], config: Vec<u8>, path: Vec<u8>, plaintext: Vec<u8>, record: Vec<u8> }

fn cases() -> Vec<Case> {
    include_str!("../../../../tests/v3/reference/differential.tsv").lines().map(|line| {
        let c: Vec<&str> = line.split('\t').collect();
        let [name, key, config, path, plaintext, record] = c[..] else { panic!("malformed case: {line}") };
        Case {
            name: name.into(), key: hex(key).try_into().unwrap(), config: hex(config),
            path: hex(path), plaintext: hex(plaintext), record: hex(record),
        }
    }).collect()
}

/// Bit positions to flip: every bit of short records, otherwise every bit
/// of the header and tag plus a spread over the body.
fn flips(len: usize) -> Vec<usize> {
    if len <= SHORT_RECORD { return (0..len * BITS).collect(); }
    let mut bits: Vec<usize> = (0..FILE_MIN_LEN * BITS).collect();
    bits.extend((0..BODY_FLIPS).map(|i| FILE_MIN_LEN * BITS + i * (len - FILE_MIN_LEN) * BITS / BODY_FLIPS));
    bits
}

#[test]
fn keyed_matches_openssl_aes_siv_byte_for_byte() {
    let all = cases();
    assert!(all.len() >= MIN_CASES);
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
            bad[bit / BITS] ^= 1 << (bit % BITS);
            assert!(decrypt_file(&config, &case.key, &case.path, &bad).is_err(), "{n}: bit {bit}");
        }
        for cut in [1, TAG_LEN, case.record.len() - FILE_HEADER_LEN] {
            if cut <= case.record.len() {
                let short = &case.record[..case.record.len() - cut];
                assert!(decrypt_file(&config, &case.key, &case.path, short).is_err(), "{n}: truncated by {cut}");
            }
        }
        for extra in [&[0u8][..], &[0u8; TAG_LEN], &case.record[FILE_HEADER_LEN..FILE_HEADER_LEN + TAG_LEN]] {
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
        let [name, password, salt, key] = c[..] else { panic!("malformed case: {line}") };
        let salt: [u8; SALT_LEN] = hex(salt).try_into().unwrap();
        assert_eq!(&derive_key(&hex(password), &salt).unwrap()[..], &hex(key)[..], "{name}");
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
    for len in 0..FILE_MIN_LEN {
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
    let mut state = SEED;
    let mut next = move || { state ^= state << SHIFTS.0; state ^= state >> SHIFTS.1; state ^= state << SHIFTS.2; state };
    // Insert, remove, flip or swap.
    const MUTATION_KINDS: u64 = 4;
    for case in cases().iter().filter(|c| c.record.len() < MUTATED_RECORD_LIMIT) {
        let (config, key, path) = (&case.config, &case.key, &case.path);
        for _ in 0..MUTATION_ROUNDS {
            let mut bad = case.record.clone();
            for _ in 0..(1 + next() % MAX_MUTATIONS) {
                let at = (next() as usize) % (bad.len() + 1);
                match next() % MUTATION_KINDS {
                    0 => bad.insert(at, next() as u8),
                    1 if !bad.is_empty() => { bad.remove(at.min(bad.len() - 1)); },
                    2 if at < bad.len() => bad[at] ^= 1 + (next() % u64::from(u8::MAX)) as u8,
                    _ if bad.len() > 1 => { let (n, j) = (bad.len(), next() as usize); bad.swap(at.min(n - 1), j % n); },
                    _ => {},
                }
            }
            if bad != case.record {
                assert!(decrypt_file(config, key, path, &bad).is_err(), "{}: accepted a mutation", case.name);
            }
            let mut random = case.record[..FILE_HEADER_LEN].to_vec();
            random.extend((0..(TAG_LEN + (next() % MAX_RANDOM_EXTRA) as usize)).map(|_| next() as u8));
            assert!(decrypt_file(config, key, path, &random).is_err(), "{}: accepted random body", case.name);
        }
    }
}
