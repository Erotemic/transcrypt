# Rust distribution of transcrypt

Status: early. See
[`docs/verification/04-dual-implementation-architecture.md`](../docs/verification/04-dual-implementation-architecture.md)
for the intended crate layout and
[`docs/verification/10-decisions-and-blockers.md`](../docs/verification/10-decisions-and-blockers.md)
for the decisions this work is waiting on.

## Crates

- `crates/transcrypt-protocol` — pure, zero-dependency byte parser and
  serializer for the repository's cryptographic object formats. Currently
  implements **detection, structural parsing and serialization of released
  legacy (v2) envelopes** only. The future secure (v3) format is deliberately not implemented here:
  its byte grammar is not frozen (D-01 pending), and nothing in this crate
  may define it by example.

Build/test without network access (no dependencies):

```console
$ cargo test --offline -p transcrypt-protocol
```

The `v2_vectors` integration test additionally exercises the parser against
blobs produced by the Bash implementation (requires `openssl` on `PATH`).

## v2 legacy format (as implemented by `transcrypt`)

A protected file is stored as **base64 text** (64-character lines, standard
alphabet, trailing newline) of a binary blob:

```text
"Salted__" || salt[8] || opaque OpenSSL ciphertext (non-empty)
```

- The base64 starts with the ASCII prefix `U2FsdGVk`, which is the only
  magic the Bash implementation checks.
- `salt` is the last 8 bytes (16 hex chars) of
  `HMAC-SHA256(key = "<path>:<password>", msg = plaintext)`; the key/IV are
  `EVP_BytesToKey(MD5, password, salt, 1)`. This crate does **not**
  re-derive or verify those values (they require the password and live in
  the future crypto adapter); it only validates and splits the structure.
- Legacy Transcrypt accepts ciphers other than AES-CBC, including AES-CTR;
  ciphertext length and padding are **cipher-specific**. The envelope parser
  cannot reject arbitrary non-block-aligned lengths without breaking valid
  v2 repositories.
- `encode_v2` emits the same canonical line-wrapped Base64 envelope as
  `openssl base64`. `base64_decode` rejects non-canonical padding and
  trailing encoded data after `=` while tolerating CR/LF line endings.
- Empty files are stored empty (the Bash filter passes them through); the
  parser therefore classifies empty input as plaintext.
- V2 is **not authenticated**. Structural acceptance does not prove a
  ciphertext is genuine, decryptable, complete, or untampered. Key/salt
  checks and legacy decryption belong to a separate crypto adapter.

The wire-format reference is
[`docs/verification/reference/v2-wire-structure.md`](../docs/verification/reference/v2-wire-structure.md).

This description is derived from the released Bash implementation (see
`docs/verification/implementation-progress.md`), not from an approved spec.


## Pure policy kernel and proof progress (2026-10-24)

`crates/transcrypt-policy` is a second zero-dependency, `no_std` Rust crate
providing preflight decisions for **future** secure staged files, unlocking,
and migration publication. It does not perform Git or crypto operations and
is not yet wired into the current legacy Bash runtime. Inputs like
`authenticated` are evidence obligations of the caller, not checks the
policy magically performs.

Both the production Base64 sextet core and the prospective policy gates have
universal fixed-width checks in `proofs/smt/`. They were locally discharged
using Z3, with Rust source fingerprints; see
[`m6-formal-bitcore.md`](../docs/verification/reference/m6-formal-bitcore.md).
The independent Lean package under `proofs/lean/` is built in a separate CI
job. Charon/Aeneas source-to-generated-Lean refinement and Rust compilation
remain distinct, mandatory acceptance gates; the SMT results alone are not
an Aeneas proof of Rust.
