//! The portable profiles (2: scrypt, 3: PBKDF2-HMAC-SHA256) against the
//! independent vectors of `tests/v3/reference/portable_vectors.py` (Python
//! hashlib and `cryptography`'s AESSIV), which the Bash client is checked
//! against too: same key, config, key-check value and records, byte for byte.

use transcrypt_rs::{config_profile, derive_key, parse_profile, Profile, ValidatedKey, KEY_SIZE};
use transcrypt_v3_core::{CONFIG_FAMILY_LEN, CONFIG_LEN, KEY_CHECK_START, SALT_LEN};

fn hex(text: &str) -> Vec<u8> {
    if text == "-" {
        return Vec::new();
    }
    (0..text.len()).step_by(2).map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap()).collect()
}

struct Vector {
    profile: Profile,
    name: String,
    password: Vec<u8>,
    salt: [u8; SALT_LEN],
    key: Vec<u8>,
    config: Vec<u8>,
    check: Vec<u8>,
    path: Vec<u8>,
    plaintext: Vec<u8>,
    record: Vec<u8>,
}

fn vectors() -> Vec<Vector> {
    include_str!("../../../../tests/v3/reference/portable-vectors.tsv")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|line| {
            let c: Vec<&str> = line.split('\t').collect();
            let [profile, name, password, salt, key, config, check, path, plaintext, record] = c[..] else {
                panic!("malformed vector: {line}")
            };
            Vector {
                profile: parse_profile(profile).unwrap(),
                name: name.into(),
                password: hex(password),
                salt: hex(salt).try_into().unwrap(),
                key: hex(key),
                config: hex(config),
                check: hex(check),
                path: hex(path),
                plaintext: hex(plaintext),
                record: hex(record),
            }
        })
        .collect()
}

#[test]
fn portable_profiles_match_the_independent_vectors() {
    let all = vectors();
    assert!(all.iter().any(|v| v.profile == Profile::Scrypt) && all.iter().any(|v| v.profile == Profile::Pbkdf2));
    let mut derived: Vec<(Profile, ValidatedKey)> = Vec::new();
    for v in &all {
        let n = format!("{:?}/{}", v.profile, v.name);
        if !derived.iter().any(|(p, _)| *p == v.profile) {
            // Key derivation, config, and the stored key file's check value.
            assert_eq!(&derive_key(v.profile, &v.password, &v.salt).unwrap()[..], &v.key[..], "{n}: key");
            let created = ValidatedKey::initialize(v.profile, &v.password, &v.salt).unwrap();
            assert_eq!(&created.config()[..], &v.config[..], "{n}: config");
            assert_eq!(config_profile(&v.config).unwrap(), v.profile, "{n}: profile");
            let stored = created.to_stored().unwrap();
            assert_eq!(&stored[KEY_CHECK_START..], &v.check[..], "{n}: key check");
            // Unlocking the committed config derives the same key.
            let unlocked = ValidatedKey::unlock(&v.password, &v.config).unwrap();
            assert_eq!(&unlocked.secret()[..], &v.key[..], "{n}: unlock");
            assert!(ValidatedKey::unlock(b"correct horse battery stapler", &v.config).is_err(), "{n}: wrong password");
            derived.push((v.profile, unlocked));
        }
        let key = &derived.iter().find(|(p, _)| *p == v.profile).unwrap().1;
        assert_eq!(key.encrypt(&v.path, &v.plaintext).unwrap(), v.record, "{n}: record");
        assert_eq!(&key.decrypt(&v.path, &v.record).unwrap()[..], &v.plaintext[..], "{n}: open");
        assert!(key.decrypt(&[&v.path[..], b"x"].concat(), &v.record).is_err(), "{n}: other path");
        for at in [22, v.record.len() - 1] {
            let mut tampered = v.record.clone();
            tampered[at] ^= 1;
            assert!(key.decrypt(&v.path, &tampered).is_err(), "{n}: tampered at {at}");
        }
        assert!(key.decrypt(&v.path, &v.record[..v.record.len() - 1]).is_err() || v.plaintext.is_empty(), "{n}: truncated");
    }
}

/// The same passphrase and salt give unrelated keys and configs under each
/// profile, and a record of one profile's config is refused under another's.
#[test]
fn profiles_never_share_keys_or_records() {
    let all = vectors();
    let scrypt = all.iter().find(|v| v.profile == Profile::Scrypt).unwrap();
    let pbkdf2 = all.iter().find(|v| v.profile == Profile::Pbkdf2 && v.name == scrypt.name).unwrap();
    assert_eq!((&scrypt.password, scrypt.salt), (&pbkdf2.password, pbkdf2.salt));
    let argon = derive_key(Profile::Argon2id, &scrypt.password, &scrypt.salt).unwrap();
    assert_ne!(&argon[..], &scrypt.key[..]);
    assert_ne!(scrypt.key, pbkdf2.key);
    let p2 = ValidatedKey::unlock(&scrypt.password, &scrypt.config).unwrap();
    let p3 = ValidatedKey::unlock(&pbkdf2.password, &pbkdf2.config).unwrap();
    assert!(p2.decrypt(&pbkdf2.path, &pbkdf2.record).is_err());
    assert!(p3.decrypt(&scrypt.path, &scrypt.record).is_err());
    // Relabelling a config's profile byte breaks its authentication: the
    // passphrase then derives another profile's key, which does not open it.
    for v in [scrypt, pbkdf2] {
        for byte in 1..=3u8 {
            let mut relabelled: [u8; CONFIG_LEN] = v.config.clone().try_into().unwrap();
            if relabelled[CONFIG_FAMILY_LEN] == byte {
                continue;
            }
            relabelled[CONFIG_FAMILY_LEN] = byte;
            assert!(ValidatedKey::unlock(&v.password, &relabelled).is_err());
            let key: [u8; KEY_SIZE] = v.key.clone().try_into().unwrap();
            assert!(ValidatedKey::authenticate(&relabelled, &key).is_err());
        }
    }
}

#[test]
fn unknown_profiles_are_named_and_refused() {
    let v = &vectors()[0];
    let mut unknown = v.config.clone();
    unknown[CONFIG_FAMILY_LEN] = 9;
    let error = config_profile(&unknown).unwrap_err();
    assert!(error.contains("profile 9") && error.contains("does not support"), "{error}");
    let error = ValidatedKey::unlock(&v.password, &unknown).err().unwrap();
    assert!(error.contains("profile 9"), "{error}");
    assert!(ValidatedKey::unlock(b"", &v.config).is_err());
    assert!(ValidatedKey::unlock(b"with\0nul", &v.config).is_err());
}
