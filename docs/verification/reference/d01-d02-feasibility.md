# D-01/D-02 feasibility evidence: deterministic AE in Bash/OpenSSL

**Status: evidence, not a decision.** This page records what the allowed
Bash runtime (the OpenSSL CLI, no extra runtime dependencies) can and cannot
compute, with reproducible commands and process inspection. It informs the
D-01 (algorithm) and D-02 (Bash feasibility) decisions in
[10-decisions-and-blockers.md](../10-decisions-and-blockers.md). Nothing
here is a cryptographic approval, and no protocol decision has been made.

Reproducer: `contrib/verification/d02-openssl-cli-probe.sh` (bash + openssl
only; writes to $TMPDIR only; safe anywhere).

## Environment where collected

- OpenSSL 3.0.13 (Ubuntu 24.04), GNU bash 5.2.21, git 2.43.0, Linux x86-64.
- Collected 2026-10-24. The probe reports n/a or fails gracefully on
  OpenSSL 1.1 / LibreSSL (no `kdf` app there) — those results are pending.

## Findings

### F-1. AEAD ciphers are not exposed by `openssl enc`

`openssl enc -list` contains no SIV, GCM, or CCM cipher (3.0.13). `enc`
cannot accept an authentication tag, so no standard AEAD (GCM/CCM/SIV) can
be driven through it. This confirms the B2 concern in
[07-audit-remediation.md](../07-audit-remediation.md).

### F-2. AES-SIV (RFC 5297) is not implementable through this CLI surface

- SIV mode is absent from `enc` (F-1).
- The S2V primitive requires AES-CMAC. `openssl mac ... CMAC` fails on
  3.0.13 ("unsupported: Algorithm (AES-256 : 0)" — the `mac` app cannot
  fetch a cipher for CMAC). CMAC availability on other 3.x minors/LibreSSL
  is unverified.
- Even where CMAC works, its only key channel in the CLI is
  `-macopt hexkey:<hex>` — the key is in **argv** (F-5).

**Consequence:** a byte-exact RFC 5297 AES-SIV implementation is not
achievable in the plain OpenSSL CLI without either (a) exposing a derived
CMAC key in argv, (b) adding a non-CLI runtime (forbidden by D-00), or
(c) changing the supported-platform policy. The Rust implementation *can*
compute SIV in-process with an audited library; the question is whether the
Bash implementation can meet the same wire bytes.

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
  vectors pass) but its 3.0.13 `pass`/`salt` parameters are inline only —
  i.e. argv — so it cannot be the product's secret channel on 3.0.0-3.0.x.
  (3.1+ adds `pass:file:`/`pass:env:`-style sources; unverified here.)

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

## Consequences for the decision register (no decisions made)

| ID | State after this evidence |
|---|---|
| D-01 | AES-SIV remains the preferred *reviewed* construction for the protocol, but **cannot be implemented in the plain 3.0.13 CLI** (F-1, F-2). Options: accept an argv-exposed derived MAC key in Bash (with a written threat-model assessment), negotiate the D-00 platform policy, or pick an alternative construction whose MAC step is expressible via the F-3/F-4 channels — each is an external decision. |
| D-02 | KDF and encryption steps are feasible with zero secret in argv on OpenSSL 3.0+ (F-3, F-4, F-6). The authentication step is **not** (F-5). |
| D-03 | PBKDF2-HMAC-SHA256 is computable; the 8-byte `-S` limit means the full public salt must be carried inside the KDF input (exact transcript to be specified). |
| D-09 | The v3 Bash format as sketched requires OpenSSL ≥ 3.0 (F-3). v2's 1.1.x/LibreSSL support is preserved only for legacy format handling. Needs a maintainer decision. |
| D-06 | `-pass fd:` gives the needed non-interactive secret channel on 3.0+ (F-6). |

## What this does NOT establish

- No cryptographic security property of any candidate construction is
  claimed. F-3/F-4 verify byte-level computation, not confidentiality or
  authenticity.
- Older-backend (OpenSSL 1.1, LibreSSL) behavior is not covered by this
  run; the probe must be executed in CI on each supported matrix entry.
- `openssl kdf`/`mac` behavior on 3.1/3.2/3.3+ (file-based kdf pass
  sources; working CMAC) is untested here.
