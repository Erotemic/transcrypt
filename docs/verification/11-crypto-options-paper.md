# 11. Cryptographic construction options paper (M1 input)

> **Historical planning context:** some requirements below were written
> before the 2026-10-25 maintainer direction. The current
> [v3 product charter](V3-PRODUCT-CHARTER.md) controls product goals,
> default UX, non-goals and review priorities; the
> [candidate wire specification](specs/V3-AUTHENTICATED-P0.md) controls
> existing ciphertext bytes. This document remains useful evidence,
> **not** an independent mandate for legacy/Bash parity or local-at-rest
> privacy in the Rust v3 product.

**Status: options under consideration — NOT approved, NOT a specification.**
This is an input to decisions D-01 (algorithm) and D-02 (Bash feasibility) in
[10](10-decisions-and-blockers.md). It records the decision space with
evidence references; choosing among these options is an external review
gate (R-07, D-01/D-02). No option here is a frozen protocol.

## 1. Fixed constraints (already agreed)

- **R-07** — the released v3 suite is authenticated deterministic
  encryption with a separately reviewed security definition; functional
  correctness alone does not establish it.
- **R-08** — new-format operations never place passwords or derived keys
  in process argv, environment, logs, or public Git metadata.
- **R-05** — same key/context/AD/plaintext ⇒ identical stored bytes.
- **R-06** — CSPRNG public salt of ≥ 128 bits, password-independent, with
  explicit context/domain separation in the KDF transcript.
- **R-19** — protected empty files have an explicit authenticated
  representation (no bare-empty pass-through).
- **D-00** — Bash distribution stays plain OpenSSL CLI (no new runtime);
  Rust uses audited in-process libraries; both must emit identical wire
  bytes for the same inputs.
- **D-00d** — v2 legacy keeps working; the new suite uses a distinct
  discriminator and is never silently reinterpreted.

## 2. Option A — RFC 5297 AES-SIV (S2V/CMAC + CTR)

The IETF-standardized deterministic authenticated mode. 32-byte key split
into K1 (S2V/CMAC) and K2 (CTR); the SIV doubles as the CTR nonce, so
`SIV || CTR_K2(SIV, P)` is fully deterministic after the key and AAD are
fixed, and it has an explicit authenticated empty record (R-19).

| Implementation | Feasibility (evidence: [d01-d02](reference/d01-d02-feasibility.md)) |
|---|---|
| Rust | **Yes** — in-process audited library; satisfies R-08. |
| Bash / OpenSSL 3.0.13 CLI | **No** — SIV absent from `enc` (F-1); CMAC broken in `mac` (F-2); CMAC keys are argv-only anyway (F-5). |

Bash sub-options if SIV is the chosen protocol:

- **A1 — argv-exposed derived CMAC key.** Bash computes the SIV steps with
  CLI primitives, accepting the derived K1 in `-macopt hexkey` argv.
  Violates R-08 in its strict form; requires a *written, risk-accepted*
  security decision (threat model: local multi-user hosts; mitigations such
  as short-lived children and `/proc` restrictions do not remove the
  exposure). Not an acceptable default without that explicit decision.
- **A2 — wait for a CLI that exposes it.** If a future OpenSSL (or
  LibreSSL) CLI gains file-keyed CMAC/SIV or a file-based MAC key, the
  same wire bytes become R-08-clean in Bash. **3.5.9 (LTS, 2026-09) does
  not**: CMAC via `mac` is still broken, `enc` still has no SIV, and `kdf`
  parameter values are still literal (see
  [d01-d02](reference/d01-d02-feasibility.md)). This option therefore
  remains a bet on a future release, not an available path.
- **A3 — Bash stays on legacy only.** Secure format is Rust-distributed.
  Contradicts the dual-implementation goal (D-00/D-00d); only if the
  maintainer elects to split the security release.

**Verdict:** A is the recommended construction for the protocol and for
the Rust implementation. The open question is *which* Bash sub-option
satisfies R-08, which is a security-review + maintainer decision.

## 3. Option B — PRF-as-MAC using only file-keyed CLI primitives

A deterministic scheme built solely from the R-08-clean channels measured
in the probe: PBKDF2/`enc -pbkdf2` (file/fd passphrase) + AES-CTR
(EVP_BytesToKey expansion) + a MAC defined as a standard PRF invocation
with the *secret* supplied through a file channel.

**Not currently CLI-feasible**: the `kdf` app (the only CLI PRF provider)
treats all `pass`/`secret`/`salt` values as literal text on both 3.0.13
and 3.5.9 — there is no file/env key channel to feed the MAC's secret
without argv exposure. Even where it is feasible, **PRF-as-MAC is not a
reviewed AE construction**; per B1 it requires its own cryptographic
review before it may be shipped. Listed so the decision is explicit, not
as a recommendation.

## 4. Option C — bespoke CBC/CTR + HMAC (October prototype family)

The unreleased `TCRYPT3:` prototype is exactly this class (synthetic-IV
CBC, encrypt-then-HMAC, 8-byte effective salt). It is **not a candidate
for approval** (B1): no standard security definition, known defects in
the reference implementation. A reworked variant (e.g. CTR +
HMAC-SHA256 with a length-prefixed transcript) would still need review
and still hits the argv-only HMAC channel on 3.0.13 (F-5). Recorded for
completeness only.

## 5. Decisions requested (external)

1. **Crypto reviewer:** confirm (or replace) RFC 5297 AES-SIV as the v3
   suite, including its S2V/CMAC parameterization, key-split, and AAD
   transcript for the context+config commitment (D-01, D-05).
2. **Security reviewer + maintainer:** if A is chosen, decide the Bash
   R-08 sub-option (A1 risk-acceptance vs A2 platform wait vs A3 scope
   split), with the D-09 platform matrix (OpenSSL ≥ 3.0? 1.1/LibreSSL
   legacy-only?) attached. Evidence status: on 3.0.13 and 3.5.9, A1 is
   the only Bash path that can compute the SIV steps at all; A2 is
   forward-looking; A3 is the only currently R-08-clean Bash outcome.
3. **Maintainer:** the `transcrypt.crypt-dir` override policy (attacker-
   writable `.git/config` can redirect script writes; see
   [implementation progress](implementation-progress.md)).

## 6. Format-versioning note

Whichever option is approved, the released suite gets a **distinct
on-disk discriminator** from the experimental `TCRYPT3:` envelope
(D-04/D-12). The suite identifier records the construction (e.g. SIV),
not the runtime that produced the bytes; both implementations must
reproduce identical bytes from it.
