//! Independent reference vectors from OpenSSL-backed Python AESSIV + argon2-cffi.
//! No Python is needed to run these Rust tests.
use transcrypt_rs::ValidatedKey;
use transcrypt_v3_core::{parse_config, parse_file_header};

mod common;
use common::hex;

#[test]
fn authenticated_vectors_and_strict_parsing() {
    let fixture = include_str!("../../../../tests/v3/reference/vectors.tsv");
    for line in fixture.lines() {
        let columns: Vec<&str> = line.split('\t').collect();
        let [name, path, plaintext, config, record] = columns[..] else { panic!("malformed vector: {line}") };
        let (path, plaintext, config, record) = (hex(path), hex(plaintext), hex(config), hex(record));
        assert!(parse_config(&config).is_ok());
        assert!(parse_file_header(&record).is_ok());
        let key = ValidatedKey::unlock(b"correct horse battery staple long secret", &config).unwrap();
        assert_eq!(key.encrypt(&path, &plaintext).unwrap(), record, "{name}");
        assert_eq!(key.decrypt(&path, &record).unwrap().to_vec(), plaintext, "{name}");
        let mut forged = record.clone();
        let last = forged.len() - 1;
        forged[last] ^= 1;
        assert!(key.decrypt(&path, &forged).is_err());
        assert!(ValidatedKey::unlock(b"not the right passphrase", &config).is_err());
        assert!(key.decrypt(b"other.secret", &record).is_err(),
                "cross-path transplant was accepted for {name}");
    }
}
