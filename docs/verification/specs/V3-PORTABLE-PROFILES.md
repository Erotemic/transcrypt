# Transcrypt v3 configuration profiles 2 and 3: portable wire contract

**Status (2026-11-11):** implemented byte-for-byte by the Rust client
(`transcrypt-rs`, `--profile=scrypt|pbkdf2`) and the portable Bash client
(`contrib/v3/transcrypt-bash`), checked against independent vectors
(`tests/v3/reference/portable-vectors.tsv`) and by two-way Git conformance
(`tests/v3/conformance/run.sh`), on OpenSSL **3.0.13**. This document
extends, and does not change, the frozen
[profile-1 specification](V3-AUTHENTICATED-P0.md): every byte of a profile-1
config and record is unchanged.

## What a profile is

A **profile** names the key-derivation function, with fixed parameters, that
turns the passphrase and the configuration's salt into the 64-byte AES-SIV
key. It is the byte after the configuration family marker. Nothing else
differs between profiles: the configuration layout, its authentication, the
records, the associated data, the key-check value and the local key file are
those of profile 1.

| Profile | Name | Key derivation (fixed parameters) | Clients |
| --- | --- | --- | --- |
| 1 | `argon2id` | Argon2id v0x13, m = 65536 KiB, t = 3, p = 1 | Rust (OpenSSL 3.0 has no Argon2id) |
| 2 | `scrypt` | RFC 7914 scrypt, N = 32768 (2^15), r = 8, p = 1 | Rust, Bash + OpenSSL ≥ 3.0 |
| 3 | `pbkdf2` | PBKDF2-HMAC-SHA256, 600 000 iterations | Rust, Bash + OpenSSL ≥ 3.0 |

All three output 64 bytes from the passphrase bytes and the 32-byte salt.
Parameters are never read from the configuration; a configuration names a
profile and the profile fixes them, so a committed configuration cannot
lower a work factor. Profile 2 needs 32 MiB of memory per derivation (128 r N
bytes); the Bash client passes OpenSSL `maxmem_bytes=67108864`, an execution
limit, not a wire parameter. New profiles need a new byte, their own
reviewed parameters and independent vectors; no other value is accepted.

## Committed configuration (55 bytes)

`config = "TCFG3" 00 || P || SALT[32] || TAG[16]`, where `P` is the profile
byte (`01`, `02` or `03`). `PREFIX = config[0:39]` and, with
`K = KDF_P(passphrase, SALT)`,

`TAG = AES-SIV(K).encrypt("", AD = ["transcrypt/v3/config", PREFIX])`.

The tag therefore authenticates the profile byte: relabelling a
configuration's profile makes the passphrase derive a different key that does
not verify it (Lean: `config_profile_bound`). A decoder checks the length, the
6-byte family marker `TCFG3 00`, and that `P` names a known profile, *before*
deriving anything; an unknown `P` is refused by name ("profile N, which this
Transcrypt does not support"), never treated as another profile.

## Records (shared by every profile)

`record = "TV3F" 00 01 || SHA256(config)[0:16] || SIV || CIPHERTEXT`

with `SIV || CIPHERTEXT = AES-256-CMAC-SIV(K).encrypt(plaintext,
AD = ["transcrypt/v3/file", config, path])` (RFC 5297; `K1 = K[0:32]` for
S2V/CMAC, `K2 = K[32:64]` for CTR, CTR counter = SIV with bits 63 and 31
cleared). The `00 01` is the **record format**, the same for every profile:
the record names its configuration by identifier, and its associated data
contains the complete configuration, profile byte included, so a record is
bound to one profile without a second marker. (The experimental profile-2
draft of 2026-11-11 used `TV3F 00 02`; it was never released and was
reconciled to the shared record format before any Rust support existed.)

Paths are the exact Git-relative bytes: 1 to 4096 bytes, no NUL, no empty,
`.` or `..` component, not `.transcrypt/…`, any `.gitattributes`, or
`.gitmodules`. Plaintext is at most 16 777 216 bytes. Decryption releases
plaintext only after the tag verifies.

## Key-check value and stored key

As in profile 1: `CHECK = AES-SIV(K).encrypt("transcrypt/v3/key-check",
AD = ["transcrypt/v3/file", config, ".transcrypt/key-check"])` (39 bytes).
Both clients store `config || K || CHECK` (158 bytes, mode 0600) in
`$GIT_COMMON_DIR/transcrypt-v3/key`, and use a stored key only when its
config is the one in force, the key verifies the config tag and the check
value opens. One unlock therefore serves either client in the same checkout.

## Passphrases

Every profile requires 16 to 4096 bytes when unlocking or choosing a
passphrase (the clients' policy; the core accepts 1 to 4096). The portable
profiles refuse NUL bytes, which a shell cannot carry; profile 1 keeps its
original rule. A new passphrase is one line. From standard input, one
trailing LF and then one trailing CR are removed. The bytes are used as they
are: no normalization or encoding conversion.

## OpenSSL 3.0 command lines (the Bash client)

```bash
# profile 2
openssl kdf -binary -keylen 64 -kdfopt hexpass:HEX -kdfopt hexsalt:HEX \
  -kdfopt n:32768 -kdfopt r:8 -kdfopt p:1 -kdfopt maxmem_bytes:67108864 SCRYPT
# profile 3
openssl kdf -binary -keylen 64 -kdfopt digest:SHA256 -kdfopt hexpass:HEX \
  -kdfopt hexsalt:HEX -kdfopt iter:600000 PBKDF2
# S2V/CMAC and CTR
openssl mac -cipher AES-256-CBC -macopt hexkey:K1 -in FILE CMAC
openssl enc -aes-256-ctr -nosalt -K K2 -iv CTR -in FILE -out FILE
```

The scrypt cost parameter is lowercase `n:` (OpenSSL refuses `N:`). The CMAC
cipher is `AES-256-CBC` (`-cipher AES-256` is not a CMAC cipher name).
`openssl enc -pbkdf2 -S` (8-byte salt) and `EVP_BytesToKey` are never used.
Before deriving a key the Bash client runs known-answer probes (AES-256-CMAC,
NIST AES-256-CTR, RFC 7914 scrypt and PBKDF2-HMAC-SHA256); a build without a
required algorithm is refused, never downgraded. Derived keys appear in local
OpenSSL arguments: an accepted local exposure under the
[charter](../V3-PRODUCT-CHARTER.md), never written to Git.

## Profile changes

A profile change is an explicit `rekey --profile=NAME` (either client for
profiles 2 and 3; only Rust can read profile 1, so converting a profile-1
repository is `transcrypt-rs rekey --profile=scrypt|pbkdf2`). It stages a new
configuration and every protected file re-encrypted, like a passphrase
change; earlier commits keep their records under the earlier configuration.
No client converts implicitly.

## Evidence

- Independent vectors: `tests/v3/reference/portable_vectors.py` (Python
  `hashlib.scrypt`, `hashlib.pbkdf2_hmac`, `cryptography` AESSIV) writes
  `portable-vectors.tsv`: per profile the key, config, key-check value and 12
  records (0/1/15/16/17/32/33/1000 bytes, NUL bytes, non-UTF-8, Unicode and
  blank-containing paths). Rust: `tests/portable_vectors.rs`; Bash:
  `tests/v3/bash/test_reference.sh`.
- Production dispatch (Lean, source-derived): `profile_kdf_spec`,
  `passphrase_ok_spec`, `derive_profile_key_spec`, `derive_config_key_spec`,
  `derive_config_key_uses_config_profile`; codec with the profile byte:
  `decode_config_exact_spec`, `parse_config_spec`, `encode_config_bytes`.
- Not proved: the security of scrypt, PBKDF2, Argon2id or AES-SIV (A10,
  A26), or the Bash source (empirical conformance only).
