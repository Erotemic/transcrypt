# Released legacy v2 wire structure: corrected interoperability contract

**Scope:** The current Bash (`transcrypt` 2.3.x) and the independent Rust
`transcrypt-protocol` crate, as of the October 24 2026 agent audit. This is
not a proposed modern encryption format and makes **no authenticity claim**.

## Bytes and cipher choice

For nonempty protected files, the committed object is encoded with OpenSSL's
standard Base64 alphabet (`+` and `/`), padded with `=`, wrapped at exactly 64
characters per line, with a trailing linefeed. Decoding yields:

```
ASCII("Salted__") (8 bytes) || salt (8 bytes) || ciphertext (>=1 byte)
```

The v2 header carries **no cipher identifier**. The cipher is chosen from
repository-local Git configuration (`transcrypt[.context].cipher`) and may be
AES-CBC, AES-CTR, or another cipher that the installed OpenSSL `enc` accepts.
Consequently **AES-CBC block alignment is not a property of the envelope**.
An AES-CBC-specific decryptor may separately enforce block/padding rules,
whereas a CTR ciphertext can have any positive length. Earlier Rust code
incorrectly rejected legitimate CTR objects that were not multiples of 16.

The Bash clean filter determines the legacy salt by taking the *final sixteen
hex characters* of a SHA-256 HMAC over the plaintext, with an HMAC key derived
from the path and password (`path:password`). This 8-byte salt is not a
modern password-independent KDF salt and must not be reused as the proposed
v3 protocol's scheme. The local password and cipher are needed for decryption.

The legacy Bash clean filter bypasses encryption of zero-length files. The
independent detector therefore classifies empty input as plaintext. All other
plaintext is not safe to infer solely from a missing or malformed prefix.

## Rust parser and serializer contracts

`parse_v2(data)` does **structural parsing only**:

1. If the Base64 prefix `U2FsdGVk` is absent, return `NotV2`.
2. Decode strict RFC 4648 Base64 (ignore CR/LF, reject data after padding,
   invalid alphabet, incorrect padding, nonzero residual pad bits).
3. Require binary bytes starting with `Salted__`, followed by eight salt
   bytes and at least one ciphertext byte.
4. Return the salt and opaque ciphertext; do not assert the selected cipher,
   digest, password, complete plaintext length, or authenticity.

`encode_v2(record)` returns an error for an empty ciphertext and otherwise
serializes the header, salt, and opaque ciphertext into the canonical wrapped
Base64 representation. Within its documented domain, the intended roundtrip
law is:

```
parse_v2(encode_v2(record)) == Ok(record)
```

This is a **candidate future Lean property**, not a theorem already proved.
A useful second law is `encode_v2(parse_v2(canonical_bytes)) == canonical_bytes`
for valid canonical blobs. CRLF-bearing or otherwise noncanonical accepted
input may normalize on reserialization.

## What these guarantees do not establish

- No ciphertext authentication, prevention of bit-flipping, or strong
  wrong-password detection. CBC padding checks are insufficient for that.
- No certainty that arbitrary truncations are detectable: with CTR, a
  shortened ciphertext can still satisfy the envelope structure.
- No invariant about the Git index, metadata, current working tree, or
  credential lifecycle. Those are separate state-machine obligations.
- No proof of the Rust parser merely because the above equations hold in
  examples. Aeneas translation and Lean theorems remain to be implemented.

## Test evidence and next proof target

`rust-legacy/crates/transcrypt-protocol/tests/v2_vectors.rs` derives a real legacy
AES-CBC blob from the OpenSSL operations used by Bash, roundtrips its bytes
through Rust parsing/serialization, and exercises AES-CTR ciphertext with a
non-block-aligned length. Unit tests cover padding-after-data rejection,
RFC 4648 examples, empty record rejection, and multiple ciphertext sizes.

**Toolchain note:** the development sandbox for this overlay lacked
`cargo`/`rustc`, so the Rust edits were not compiled there. The checked-in
GitHub Actions Rust job runs `cargo test --offline`. Verify that job and run
it locally before treating the revised Rust crate as accepted evidence.
