# Transcrypt v3 portable profile 2: Bash/OpenSSL wire contract

**Status (2026-11-11):** Implemented in `contrib/v3/transcrypt-bash` and
checked against independently generated AES-SIV/scrypt byte vectors on
OpenSSL 3.5.5. **OpenSSL 3.0.13 is the intended minimum and still requires a
run on that target version. Rust profile-2 dispatch and formal refinement are
pending.** The identifiers here are allocated to *profile 2*; this document
is a new protocol, not a change to the frozen
[Argon2id/Rust profile 1](V3-AUTHENTICATED-P0.md).

## Threat model and observable guarantees

Selected paths must enter *published Git blobs* as authenticated ciphertext.
The attacker's information includes the repository, its configuration,
all reachable historical Git objects and ciphertext chosen for substitution,
truncation or tampering. The attacker does not possess the passphrase and
does not compromise the unlocked developer machine. Local process argument
secrecy, zeroization, temporary plaintext and credential persistence are
optional hardening. Credentials and plaintext **staged into Git** are real
security violations. Local hooks are defense in depth, not remote protection
against a malicious committer; deploy a server hook for remote enforcement.

## Cryptographic primitives

- KDF: RFC 7914 **scrypt**, parameters `N=32768`, `r=8`, `p=1`, `dkLen=64`.
  Salt is exactly 32 uniform random bytes, generated once on `init` or
  `rekey`. Password bytes are passed unchanged: no normalization, implicit
  terminator, line ending or encoding conversion. The Bash interface supports
  1–4096 non-NUL passphrase bytes for unlocking; `init` and `rekey` enforce
  at least 12 bytes as a user-facing creation policy. The local OpenSSL KDF
  memory budget is `maxmem_bytes=67108864`; this is an execution ceiling,
  **not** a variable wire parameter.
- AES-256-CMAC-SIV, RFC 5297, 64-byte derived key `K = K1 || K2`, first
  32 bytes for CMAC/S2V, final 32 bytes for AES-CTR; no random IV/nonce per
  record. For associated-data bytestrings `[A1, ..., An]`, compute
  `S2V(K1, [A1, ..., An], plaintext)`, using CMAC(128-bit zero block) as
  its initial value, RFC doubling reduction polynomial `0x87`, and RFC
  padding for plaintext shorter than 16 bytes. Clear the top bit of bytes
  **8 and 12** in the 16-byte SIV tag for the CTR initial block.
- Config ID: first 16 bytes of SHA-256 of all 55 config bytes.
- Maximum plaintext: **16,777,216 bytes**. Reject oversized records and
  plaintext without truncation. All binary bytes are significant.

An OpenSSL 3.0 CLI KDF invocation is:

```bash
openssl kdf -binary -keylen 64 \
  -kdfopt "hexpass:$PASSWORD_HEX" -kdfopt "hexsalt:$SALT_HEX" \
  -kdfopt 'n:32768' -kdfopt 'r:8' -kdfopt 'p:1' \
  -kdfopt 'maxmem_bytes:67108864' SCRYPT
```

Both `hexpass` and `hexsalt` mean the *binary* bytes denoted by hex. No
`openssl enc` password derivation, `-S` (8-byte salt), `EVP_BytesToKey`,
MD5, AES-CBC fallback, or unauthenticated mode is used. The Bash adapter
calls `openssl mac -cipher AES-256-CBC -macopt hexkey:... CMAC` and
`openssl enc -aes-256-ctr -K ... -iv ... -nosalt` to compose AES-SIV.
Local command-line keys are accepted under the stated threat model.

## Exact committed config

`config = ASCII("TCFG3") || 00 02 || SALT[32] || TAG[16]`

Total length is **55 bytes**. Compute `KEY = scrypt(passphrase, SALT, ...)
`, `PREFIX = config[0:39]`, then:

`TAG = AES-SIV(KEY).encrypt(empty, AD=["transcrypt/v3/config", PREFIX])`

For empty plaintext AES-SIV produces precisely the tag. Before persisting
an unlocked key, compare the entire computed authentication tag. Unknown
or unsupported config IDs fail without fallback. A profile-1 config begins
`TCFG3 00 01` and must remain byte-for-byte unchanged.

## Exact Git blob record

`record = ASCII("TV3F") || 00 02 || SHA256(config)[0:16] || SIV || CIPHERTEXT`

Total length is **38 + N** bytes. `SIV || CIPHERTEXT` is RFC 5297
AES-256-CMAC-SIV with:

`AD=["transcrypt/v3/file", complete_config_bytes, canonical_git_path_bytes]`

Git-relative path bytes use forward slashes, must contain 1–4096 bytes,
no NUL, `.` or `..` components, double separators or absolute prefix.
`.transcrypt/*`, any `.gitattributes`, and root `.gitmodules` are reserved.
No character-set normalization is performed. Paths are selected by Git's
effective `filter=transcrypt-v3` attribute (usually the committed `transcrypt`
macro). Encryption is deterministic, so equal bytes at the same path under
the same config yield equal records. Historical equality and rollback remain
observable. Renames require encryption under the new path.

A decryptor must check the header, size, profile and config ID; decrypt to
an unpublished temporary buffer/file; recompute S2V over the exact AAD;
and release plaintext **only after** a tag match. It must reject wrong
paths, wrong configurations, modified or truncated records and unsupported
profiles without outputting plaintext. A locked smudge may retain a
structurally plausible ciphertext record as ciphertext, never as plaintext;
commit-time verification requires an unlocked key.

## Local credential and conversion policy

The standalone Bash adapter persists the authenticated 55-byte config and
64-byte derived key (119 bytes total) in
`$GIT_COMMON_DIR/transcrypt-v3/bash-key-p2`, not in Git config or the
worktree. The original passphrase is never stored. `lock` removes the file;
`hydrate` can decrypt an already-checked-out encrypted file after unlocking.
`audit REV` selects the config from that revision and authenticates records
using the active or locally preserved historical key. The pre-push hook
checks every outgoing revision, including intermediate commits. Missing
historical keys cause an explicit refusal; local hooks can still be bypassed
by an authorized operator, so a remote enforcement policy is separate.
`rekey` stages a new config and fresh SIV blobs, and saves the previous local
key under `bash-key-p2.previous-<old_config_id>` to assist historical
recovery. This local layout is *not* a publication/wire requirement.

Profile conversion must be an explicit full re-encryption operation; never
silently reinterpret profile-1 records under profile 2. An independent Rust
implementation must use this exact profile, including salt size, KDF output,
S2V framing and path rules, to establish byte-identical parity.

## Evidence and remaining work

- Independent vectors: `tests/v3/bash/portable-p2-vectors.tsv`, generated
  using Python `hashlib.scrypt` and `cryptography` `AESSIV`, not Bash/OpenSSL.
- Runner: `tests/v3/bash/test_reference.sh` (Bash, Git, OpenSSL, Unix tools);
  tests exact records, empty/binary/boundary plaintext, tampering, wrong
  path/password, locked behavior and real-Git lifecycle.
- Pending: actual OpenSSL 3.0.13 run, Rust adapter and Rust/Bash two-way
  comparison, source-derived Lean profile-2 proofs, Git conflict/fault and broader clone matrix, security review and legacy-v2 migration.
