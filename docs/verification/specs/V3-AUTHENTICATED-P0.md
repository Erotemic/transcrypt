# Transcrypt v3 secure-first proof of concept: canonical byte contract

**Status:** Proposed experimental v3 protocol. No compatibility with released
legacy formats or the earlier `TCRYPT3:` experiment. The Rust implementation
must be built/tested and independently reviewed before security-sensitive use.
This document is **independent of the Rust source** and is the intended
reference for a future Bash implementation and Lean refinement proofs.

## Scope

One context, one protected filename policy (`*.secret`), one fixed crypto
suite, and these actions: `init`, `unlock`, `clean`, `smudge`, `verify-index`,
`hydrate`, `lock`. No migration, rekey, nested contexts, GPG, merge driver,
streaming files larger than 16 MiB, or implicit plaintext fallbacks.

## Constants and primitives

- Password KDF: **Argon2id v=19**, `m=65536 KiB`, `t=3`, `p=1`, `output=64 bytes`.
- Salt: 32 bytes from the operating system CSPRNG, generated once per repo.
- AEAD: **AES-256-CMAC-SIV** per RFC 5297, 64-byte key, **deterministic**
  (no nonce), 16-byte authentication tag followed by ciphertext.
- Associated data is an **ordered list** of bytestrings, not concatenated
  data. The order matters and follows RFC 5297 S2V.
- Config identifier: first 16 bytes of SHA-256 of the **complete committed
  config bytes**; identifier is only a fast public discriminator, not an
  authentication mechanism.
- Maximum plaintext: 16 MiB. Reject oversized input before crypto.
- A wrong version, wrong password, wrong config, or corrupt ciphertext
  always **fails**; never pass through original bytes as plaintext.

## Committed `.transcrypt/config`

Fixed length **55 bytes**; no variable configuration parsing:

| Offset | Length | Contents |
|---|---:|---|
| 0 | 7 | ASCII `TCFG3`, then `00 01` |
| 7 | 32 | random repository salt |
| 39 | 16 | AES-SIV encryption of empty plaintext |

Compute key `K = Argon2id(passphrase, salt, 65536, 3, 1, outLen=64)`.
Let `prefix = config[0:39]`. The final 16-byte authenticator is:

`AES-SIV(K).encrypt(plaintext=b"", AD=[b"transcrypt/v3/config", prefix])`

An unlock must validate the tag with the derived key **before** persisting
credentials, installing filters, or hydrating plaintext.

## Protected file object

`record = header || AES-SIV(K).encrypt(plaintext, AD)` where the header is:

| Offset | Length | Contents |
|---|---:|---|
| 0 | 6 | ASCII `TV3F`, then `00 01` |
| 6 | 16 | SHA-256(config bytes)[0:16] |
| 22 | 16+N | AES-SIV tag (16 bytes) followed by N ciphertext bytes |

`AD=[b"transcrypt/v3/file", complete_config_bytes]`.

An empty plaintext is valid (`N=0`, total record length 38 bytes).
The selected AES-SIV mode is deterministic and **leaks equality of identical
files in the same repository**. Records are NOT path-bound; copying an
otherwise valid ciphertext to another protected pathname in the same
repository can succeed. Repository/metadata substitution, modification,
and cross-repository ciphertext replay fail unless the corresponding key and
config bytes also match. Old valid repository snapshots can still be rolled
back by adversaries controlling Git history; freshness requires separate
trusted state and is outside this POC.

## Stateful lifecycle and key management

- `init`: require an ordinary Git repository, no `.transcrypt` or
  `.gitattributes`, and no conflicting pre-commit hook. Generate metadata,
  install Git filters, install a local hook, and stage the public config and
  `*.secret` attributes with `-diff` (no textconv cache). Explicitly committing those files is required.
- `unlock`: derive from a terminal passphrase or opt-in stdin, verify the
  config **first**, then provision a process-local key file under
  `.git/transcrypt-v3/key` with mode `0600` and directory mode `0700`.
  This is the **prototype's explicit local-key-at-rest compromise**; it is not
  an OS keyring or memory-only agent and needs replacement for strong
  endpoint-at-rest protection.
- `clean`: accept plaintext only, emit a complete authenticated record only
  after successful encryption. Do not double-encrypt recognizable records.
- `smudge`: authenticate and then release plaintext; reject all other bytes.
  Git diffs are disabled for protected files rather than invoking textconv.
- `verify-index`: check staged `.transcrypt/config` exactly matches worktree
  config; staged `.gitattributes` equals the fixed policy; every index
  `*.secret` is a regular Git blob decryptable using the active config/key.
  A Git hook only guards cooperating local commits; it is bypassable and does
  not enforce remote policy.
- `hydrate`: only for fresh clones containing raw ciphertext in worktree.
  Preflight all protected paths against the Git index before `git restore`.
  Never discard locally modified protected files.
- `lock`: preflight no dirty or untracked protected files; overwrite tracked
  plaintext working files with the exact ciphertext in the index and then
  remove the local key. This is NOT certified secure deletion, atomic across
  multiple files, or protection against plaintext in Git textconv notes,
  caches, snapshots, swap, or backups.

For production hardening, the trusted OS/Git adapter should also eliminate
local-key persistence, make unlock/lock crash-transactional, close path
races, address very large files, and add explicit rollback protection if
required by the threat model. These obligations are **not** discharged by
correctness proofs for the pure Rust format parser.

## Machine checkability and implementation correspondence

- `rust/crates/transcrypt-v3-core/src/lib.rs`: pure `no_std` implementation
  of fixed-length encoders and strict envelope parsers. Intended Aeneas
  extraction target; no RustCrypto dependencies in this crate.
- `rust/crates/transcrypt-v3/src/lib.rs`: KDF and AES-SIV adapter invoking
  external cryptographic libraries. Their algorithmic correctness and
  constant-time behavior are separate trusted assumptions.
- `rust/crates/transcrypt-v3/src/main.rs`: Git/OS adapter, to be tested under
  fault injection and eventually related to a transition specification.
- `tests/v3/reference/check_vectors.py`: independent Python reference using
  argon2-cffi and OpenSSL-backed `cryptography.AESSIV`; generates committed
  hex vectors in `vectors.tsv`, also consumed by Rust tests.
- `proofs/aeneas/translate-v3-core.sh`: reproducible translation entrypoint.
  No claims of Aeneas-generated Lean refinement until code is actually
  extracted, built, and proved against an independent Lean specification.

Bash correspondence: the released Bash 2.x and draft v3 script have **not**
been changed to support this format. They must implement exactly the same
ordered AAD and record grammar to become interoperable. Existing Bash
legacy behavior is not a requirement on this secure-first Rust implementation.

Correspondence and proof obligation map: [`v3-core-traceability.md`](../reference/v3-core-traceability.md).
