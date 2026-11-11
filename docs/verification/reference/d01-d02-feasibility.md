# D-01/D-02 feasibility evidence: deterministic AE in Bash/OpenSSL

**Status: corrected feasibility evidence (2026-11-11), not completed Bash v3 conformance.** This page records what the allowed
Bash runtime (the OpenSSL CLI, no extra runtime dependencies) can and cannot
compute, with reproducible commands and process inspection. It informs the
D-01 (algorithm) and D-02 (Bash feasibility) decisions in
[10-decisions-and-blockers.md](../10-decisions-and-blockers.md). Nothing
here is a cryptographic approval, and no protocol decision has been made.

Reproducer: `contrib/verification/d02-openssl-cli-probe.sh` (bash + openssl
only; writes to $TMPDIR only; safe anywhere).

## Environment where collected

- OpenSSL 3.0.13 (Ubuntu 24.04 system), GNU bash 5.2.21, git 2.43.0,
  Linux x86-64. Collected 2026-10-24.
- OpenSSL 3.5.9 (LTS) built from source (`no-asm`, `/tmp/openssl35`) and
  probed the same day. (Build note: the stock x86-64 assembly build in 3.5
  emits huge loop-expansion intermediates; `no-asm` is sufficient for CLI
  behavior.)
- The probe reports n/a or fails gracefully on OpenSSL 1.1 / LibreSSL
  (no `kdf` app there) — those results are pending (CI job).

## Findings

### F-1. AEAD ciphers are not exposed by `openssl enc`

`openssl enc -list` (3.0.13 and 3.5.9) contains no SIV, GCM, or CCM cipher.
GCM/CCM exist as library algorithms in 3.5.9 (`list -cipher-algorithms`) but
the `enc` app does not take an authentication tag, so no standard AEAD
(GCM/CCM/SIV) can be driven through it. This confirms the B2 concern in
[07-audit-remediation.md](../07-audit-remediation.md).

### F-2. AES-SIV (RFC 5297) can be composed from CLI primitives

The previous **negative CMAC result was a faulty probe**, not an OpenSSL
limitation. The probe specified `-cipher AES-256`; the supported cipher
name is `AES-256-CBC`. On the target machine, **OpenSSL 3.0.13** returned
`0020215DA5F0F80C30C12D5FF18F7F4A` for this command (reported by the
maintainer on 2026-11-11):

```bash
printf test | openssl mac -cipher AES-256-CBC \
  -macopt hexkey:0000000000000000000000000000000000000000000000000000000000000000 CMAC
```

The same vector was independently reproduced with OpenSSL 3.5.5. OpenSSL's
3.0 `mac` documentation names AES-256-CBC as a valid CMAC cipher. `enc`
still does not expose AES-SIV as one switch (F-1), so a Bash port must
compose **RFC 5297 S2V with CMAC** and **AES-256-CTR** in binary-safe
Bash/CLI operations. CMAC accepts a derived key via
`-macopt hexkey:<hex>` (argv exposure, accepted under the new threat model).
The complete S2V composition, counter-bit masking, empty records, binary
handling and wire equivalence still require a tested prototype; **this is
feasibility, not an implemented Bash v3 or a cryptographic review**.

**Follow-up:** fix `contrib/verification/d02-openssl-cli-probe.sh`'s CMAC
cipher argument and replace the negative result with a positive known-answer
probe in the D1 work package. This docs-only change does not alter the
script, so older probe output remains stale until that task lands.

### F-2a. Portable 64-byte scrypt derivation is an OpenSSL 3.0 path

The OpenSSL 3.0 `kdf` CLI exposes `SCRYPT` with `hexpass`, `hexsalt`,
`n`, `r`, `p`, `maxmem_bytes`, and selectable key length; `PBKDF2` is an
alternative. The target is a complete **32-byte repository salt** and
**64-byte derived key** with fixed profile-specific parameters. The CLI
places password bytes in argv (accepted local trust assumption). Unlike
`enc -pbkdf2 -S`, this path does **not** truncate salts to eight bytes.
The exact 3.0.13 output, parameter availability, memory limits and
independent vectors remain a D1 prototype/test requirement. Argon2id is
not available from the OpenSSL 3.0 CLI KDF and remains Rust-only on 3.0.

### F-3. PBKDF2-HMAC-SHA256 without secret in argv: feasible on OpenSSL 3.0+

`openssl enc -e -<cipher> -pbkdf2 -iter N -md sha256 -S <8-byte hex salt>
-pass file:…` (or `-pass fd:N`) derives the cipher key with
PBKDF2-HMAC-SHA256(passphrase, salt, N, 48), key = first 32 bytes, iv =
next 16. Verified byte-exact against an independent pycryptodome
computation (probe sections 3; constants in the script).

Constraints:
- `-S` accepts at most 8 bytes of salt (longer input is ignored with a
  warning). A 128-bit public salt (D-03) therefore cannot ride in `-S`
  alone; it must be folded into the passphrase bytes (exact layout to be
  frozen in the spec) or the support matrix narrowed.
- `-pbkdf2` exists only in OpenSSL 3.0+; it is **not** available in
  OpenSSL 1.1.x or LibreSSL. This is the main platform-matrix impact
  (D-09): a v3 Bash format built on `-pbkdf2` drops the older backends
  currently supported by v2.
- The `openssl kdf` app (3.0+) computes PBKDF2 correctly (both RFC 7914
  vectors pass on 3.0.13 and 3.5.9), but **its `pass`/`salt` (and other
  text) parameter values are literal strings in both versions**: the value
  prefixes `hex:`, `file:`, `env:` are *not* expanded (verified against
  independent computations and against the 3.5.9 parameter-parsing source;
  a 3.5.9 `pass:file:<path>` does not even open the file). Only *key-name*
  prefixes (`hexpass:`, `hexsalt:`, …) decode. The probe's section 7
  records this classification per build. Therefore **the `kdf` app is not
  a secret channel on 3.0.13 or 3.5.9** — the `enc` app's `-pass` remains
  the only file/fd secret channel.

### F-4. Raw-key AES-CTR/ECB without secret in argv: feasible on 3.0+

`openssl enc -<cipher> -nosalt -md sha256 -pass file:…|fd:…` uses
`EVP_BytesToKey(SHA-256, passphrase, salt=NULL, iter=1)`: key =
SHA256(pass), iv = SHA256(key || pass)[:16]. Verified byte-exact for
AES-256-CTR (16-byte big-endian +1 counter, no padding) and AES-256-ECB
(PKCS7). This is a documented, reproducible expansion a Rust
implementation can compute directly.

### F-5. Every CLI keyed-MAC channel puts the key in argv

- `openssl mac -macopt hexkey:<hex> <MAC>` (HMAC, CMAC, …) and
  `openssl dgst -macopt hexkey:<hex>` accept the key only as an argv
  string; `key:file:`/`key:hex:` are treated as literal text on 3.0.13.
- Process inspection (probe section 5): for `-pass fd:`/`-pass file:`
  invocations the passphrase is **not** present in child argv or environ
  (only the file path / fd number); for `-macopt hexkey:` the key **is**
  present in argv. Same class of exposure as audit finding A6, applied to
  a derived key.

### F-6. Password acquisition for non-interactive filters

`-pass fd:N` works (identical output to `-pass file:`), so a Git filter
process can receive the password on a dedicated pipe without argv, env,
or a temporary file. This satisfies the D-06 capability requirement for
the KDF step on 3.0+ backends.

## Consequences for the current decision (2026-11-11)

- **D-01/D-02:** retain RFC 5297 AES-256-CMAC-SIV and path/config binding;
  the `enc` command does not itself support SIV, but CLI CMAC+CTR
  composition is the active approach. Accept local argument-list exposure
  of password and derived key for Bash.
- **D-03:** preserve Rust P1 Argon2id unchanged. Specify separately
  versioned scrypt/AES-SIV (portable preferred) and PBKDF2/AES-SIV
  (portable alternative), with 32-byte public salts and 64-byte derived
  outputs, after parameter calibration and independent test vectors.
- **D-06:** a special FD-only secret channel is no longer a requirement for
  the Bash implementation; ensure secrets do not enter published Git.
- **D-09:** OpenSSL **3.0.13** is the first-class target. Actual provider
  capabilities are probed; older OpenSSL and LibreSSL do not acquire v3
  support merely because they supported legacy Bash v2.
- **Versioning:** P1 discriminators remain frozen. New profiles get new
  discriminators/config contracts and fail closed on unsupported clients.

See [the active plan](../V3-DUAL-IMPLEMENTATION-ROADMAP.md) and
[product charter](../V3-PRODUCT-CHARTER.md).

## What this does NOT establish

- No cryptographic security property of a proposed new profile is
  claimed. F-3/F-4 verify byte-level computation, not confidentiality or
  authenticity.
- OpenSSL 1.1.x / LibreSSL behavior is not covered by these runs; the CI
  `feasibility-probe` job collects it on the hosted matrix. (Expected:
  no `kdf` app; no `enc -pbkdf2`; `-pass file:/fd:` and `enc` core ciphers
  still work — to be confirmed, not assumed.)
- Behavior on OpenSSL 4.x (3.6/4.0 exist in this era) is untested; the
  probe's section 7 is designed to detect any future file/env key-channel
  changes.
