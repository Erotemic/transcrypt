# Reference: experimental October 2026 Bash `TCRYPT3` protocol

**DESCRIPTIVE ONLY — NOT AN APPROVED PROTOCOL, NOT RELEASED.** This page
records the byte calculations of the supplied development overlay so that
Bash and Rust researchers can reproduce old experiments. It must not be
mistaken for the future secure-format specification in
[02](../02-protocol-and-wire-format.md). The security audit identified
several release-blocking defects in the prototype.

Provenance:

- Upstream parent: `elasticdog/transcrypt-v3` at
  `fcf94da40f31110122577b857a1102ff4a486cf3`.
- Experimental code: `transcrypt-v3-authenticated-pbkdf2-final-overlay.tar.gz`,
  especially Bash functions `v3_load_keys`, `v3_encrypt_file`,
  `v3_decrypt_file`, `write_v3_config`, `git_clean`, `git_smudge`.
- Security report: `transcrypt-v3-security-audit-2026-10-23.md`.
- All example credentials are artificial; do not use a fixed example salt
  for any production repository.

## Recognized non-secret config

One accepted example (not a recommendation):

```ini
[transcrypt]
format = v3
cipher = aes-256-cbc
digest = sha256
kdf = pbkdf2
iterations = 250000
base-salt = 000102030405060708090a0b0c0d0e0f
auth = hmac-sha256
```

The prototype's Bash validator accepts a `format = v3` config with
`cipher = aes-256-cbc`, `digest = sha256`, `kdf = pbkdf2`, `auth = hmac-sha256`,
100000..10000000 iterations, and 32 hex characters of public salt. It
rejects some unsupported keys but is **not** a proven duplicate-key/canonical
config parser. The default new-repo iteration count is 250000.

## Exact high-level byte calculations

Define byte concatenation as `||`, HMAC = HMAC-SHA256, SHA256 output 32 bytes,
`hex` as lowercase ASCII hex encoding; `first8`, `first16` select bytes.
The *input* `salt_hex` is the 32-character public salt in text form, not its
16 decoded bytes.

```text
kdf_transcript = ASCII("transcrypt/v3/kdf/") || ASCII(context)
                 || ASCII("/") || ASCII(salt_hex)
effective_salt = first8(SHA256(kdf_transcript))
master = PBKDF2_HMAC_SHA256(password, effective_salt, iterations, 32 bytes)
enc_key = HMAC(master, ASCII("transcrypt/v3/encryption"))
mac_key = HMAC(master, ASCII("transcrypt/v3/authentication"))
iv_key  = HMAC(master, ASCII("transcrypt/v3/synthetic-iv"))

iv = first16(HMAC(iv_key, ASCII("transcrypt/v3/iv") || 0x00 || plaintext))
C  = AES_256_CBC_PKCS7_Encrypt(enc_key, iv, plaintext)
b64 = standard_base64(C), one line without internal whitespace
tag = HMAC(mac_key, ASCII("TCRYPT3:") || hex(iv) || ASCII(":") || b64)
record = ASCII("TCRYPT3:") || hex(iv) || ASCII(":") || hex(tag)
         || ASCII(":") || b64 || LF
```

Wire example shape:

```text
TCRYPT3:<32 lowercase hex IV>:<64 lowercase hex MAC>:<base64 ciphertext>\n
```

That syntax line is illustrative: the angle-bracket segments are descriptive,
not literal bytes in a valid record.

The prototype normally passes an **empty plaintext** through as an **empty
Git blob** instead of emitting authenticated ciphertext. Its new secure
format should not automatically inherit that choice.

Decryption reads/parses a one-line record, checks the expected HMAC over the
ASCII transcript before AES-CBC decryption, writes a temporary decrypted
file, and verifies that the synthetic IV recomputes correctly. The Bash
comparison uses shell string equality rather than a proven constant-time MAC
comparison. Git filter I/O and temp files form additional assumptions beyond
this byte calculation.

## Known limitations — do not promote to final spec

1. **Salt reduction:** 16-byte public salt string is hashed then truncated
   to an effective **8-byte** PBKDF2 salt because of the `openssl enc -S`
   interface. This reduces the salt domain and deviates from the goal of
   at least 128-bit public salt input directly used in key derivation.
2. **Bespoke cipher design:** synthetic-IV AES-CBC and HMAC is not itself a
   reviewed standardized deterministic AE mode; interoperability tests do
   not prove confidentiality/authentication for arbitrary inputs.
3. **Secret-in-argv:** `openssl enc -K` and `dgst -macopt hexkey` expose
   derived keys via process arguments; `-pass env:ENC_PASS` additionally
   transports a password in a child-process environment.
4. **Unbound file identity:** authenticates the blob contents under a
   context-derived key, but does not bind the file path, tree/commit identity,
   or freshness. Same-context substitution and replay are possible.
5. **No authenticated empty representation:** empty protected blob lacks
   secure authentication; this must be explicitly resolved.
6. **State/operational defects:** missing staged config, salt changes,
   cached plaintext, wrong-password persisted settings, symlink redirect,
   magic-only pre-commit checks, and pathname splitting were reproduced in
   the October 23 audit. See [07](../07-audit-remediation.md).
7. **Not yet portable/verified:** no independent cross-version cryptographic
   analysis, no completed Rust proof of this candidate, no universal
   OpenSSL/LibreSSL guarantee.

Do **not** repurpose the existing `TCRYPT3:` marker to mean a different
algorithm without an explicit compatibility/migration decision. Prefer a
distinct version discriminator for the eventual reviewed secure format, even
if the user-facing product release remains called "Transcrypt v3".

## Test-vector provenance

An exploratory foundation in the prior workspace generated a fixed vector
using the prototype. That can serve as a **candidate-regression** vector to
prove faithful reverse engineering, but not as the independent golden
reference for the future secure format. Any eventual frozen golden vector
must be calculated independently from its approved algorithm specification.
