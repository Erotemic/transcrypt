# 10. Decision register: what is agreed and what must be decided

> **Current maintainer direction (2026-10-25):** consult the
> [v3 product charter](V3-PRODUCT-CHARTER.md). Generic Git attribute selection,
> persistent local-derived credentials as the default, an optional in-memory
> agent/private-workstation mode and recoverable one-time legacy transition
> are the current product goals. The historical Bash dependency and
> local-at-rest decisions below do not override them.
>
> **Historical decision register:** These proposed choices were written
> before the narrow Rust-first Argon2id/AES-SIV v3 prototype. Some conflict
> with the current experimental v3 candidate (especially D-03 Argon2id,
> D-08 pathname binding, and the out-of-scope list). Do not use this file
> to block active Rust v3 formalization or to claim its profile is already
> reviewed. See [V3-ROADMAP](V3-ROADMAP.md) for active decisions; keep this
> register for future Bash-portability and upstream-governance work.

**This table distinguishes prior maintainer decisions from new proposals.**
Do not label a design "agreed" merely because this planning document proposes
it. All blocking entries need a recorded decision before the final wire
format is written or released.

## A. Agreed external constraints / project commitments

| ID | Decision / constraint | Status | Basis |
|---|---|---|---|
| D-00 | Keep Bash + OpenSSL standalone, no new Python/Rust runtime dependency | Agreed upstream constraint | Maintainer issue #134 |
| D-00a | Develop against `transcrypt-v3` in small PRs; keep v2 Bats regression suite | Agreed upstream process | PR #210, #211, issue #134 |
| D-00b | PBKDF2 + committed non-secret settings + explicit migration + safe failure handling form the agreed broad v3 roadmap | Agreed broad scope, not final algorithm | Issue #134 |
| D-00c | Alternative Rust distribution + Lean/Aeneas formal verification, common spec | User-selected project direction; not upstream-maintainer-approved | Current project request |
| D-00d | Cryptographic format/release cannot silently break existing v2 repository clones | Broad shared requirement | Issue #134 and PR #136 discussions |

## B. Blocking decisions before protocol freeze

| ID | Question | Recommended direction / concrete experiment | Gate and evidence |
|---|---|---|---|
| D-01 | Which authenticated deterministic encryption algorithm? | First evaluate RFC 5297 AES-SIV (deterministic mode); reject treating October's bespoke CBC/HMAC prototype as approved | Crypto expert review, published security definition, two independent sets of vectors |
| D-02 | Can Bash implement that algorithm with **only** its allowed runtime safely? | Prototype required primitive invocations on supported OpenSSL/LibreSSL versions; no user-space hand-rolled cryptography accepted without review; no secret keys in argv | Real OS process inspection and cross-version byte-for-byte tests; otherwise revise platform/dependency policy before shipping |
| D-03 | Exact KDF work factor, salt/domain transcript, and secret expansion? | PBKDF2-HMAC-SHA256 initially, >=128-bit independently generated public salt, explicit context/version separation; calibrate runtime without weakening offline-guess resistance | Published literal values, bounds and known-answer vectors; cross-implementation comparison |
| D-04 | Immutable envelope/version identifier and encodings? | Distinguish released scheme from provisional `TCRYPT3:`; do not overload the same discriminator with incompatible bytes | Exact grammar and unknown-version failure test |
| D-05 | Canonical public metadata and config/hash commitment? | Strict canonical Git-config-compatible subset; require exact suite, iterations, salt, version; authenticate config/context in every record | Full grammar, digest transcript, missing/duplicate/changed-config vectors |
| D-06 | Password/key acquisition for non-interactive Git filters? | Secret FD/TTY-based unlock, no argv/env; opt-in persistence with permissions and threat model; legacy credentials isolated | Bash/Rust capability proof-of-concept and process observation; unlocked clone scenarios |
| D-07 | Empty protected files and arbitrary plaintext beginning ciphertext magic? | Authenticated empty record; ambiguous-prefix plaintext must not be bypassed. Define explicit collision/error behavior | Canonical zero-length and magic-prefix test vectors |
| D-08 | Bind ciphertext to path, stable ID, or only context/config? | Default path-independent authenticated blobs for reliable Git rename/merge; explicitly allow valid same-context transplant | Maintainer/security sign-off and rename/merge tests; if path binding selected, new ID/lifecycle scheme required |
| D-09 | Which exact crypto backends and platform versions are supported? | Probe capabilities rather than trusting version strings; unsupported secure suite fails closed | Published OpenSSL/LibreSSL/Bash/Git matrix and CI |
| D-10 | What is realistic transaction atomicity for Bash vs Rust? | Temporary index, pinned tree, preflight, journal/recovery; formalize observable rollback; no assertion of universally atomic multi-file FS updates | Crash/fault matrix, local filesystem limitations documented |
| D-11 | Rust source location / upstream ownership? | Prefer optional companion distribution; put shared spec where maintainer accepts it, avoid forcing Rust CI on Bash maintainer | Governance/release maintainer acknowledgment |
| D-12 | How to treat the previous prototype's on-disk records? | Treat unreleased `TCRYPT3:` as development fixtures; if anyone deployed them, provide explicit one-time conversion tool rather than silent reinterpretation | Provenance and real-world usage assessment |

These 12 entries are **not yet approved**. D-01 through D-07 are hard
blockers for encryption format implementation; D-08/D-09 need approval before
claiming cross-host interoperability; D-10 before migration; D-11 before
upstream packaging; D-12 before format publication.

## C. Selected engineering defaults pending final confirmation

These are strong proposals to make implementation planning actionable:

1. Secure scheme and legacy v2 use **separate decoders and no fallback** from
   a failing secure decoder.
2. New repos with ordinary unencrypted commits select secure defaults once
   the new scheme is available; pre-existing legacy encrypted repos do not
   auto-upgrade.
3. Every protected path and associated public config are validated in the
   **staged** tree before a cooperative commit; do not confuse that with a
   universally enforced server policy.
4. Rekey normally regenerates the public salt and produces a complete
   re-encryption transition; there is no routine "edit the salt" operation.
5. Model parsing and state decisions in pure safe Rust for first Aeneas
   extraction; crypto and Git effects are opaque trusted adapters initially.
6. Bash source review includes explicit function-to-spec correspondence and
   failure paths, with revisioned evidence; no claim of machine-checked Bash.
7. No plaintext caching through Git textconv notes in secure mode; legacy
   cache remediation warns about backups, refs, reflogs and unreachable data.
8. Both Bash and Rust agree on *outcome class* and ciphertext bytes, not
   necessarily word-for-word human-facing warning text.
9. Release claims state verified Rust function coverage and remaining
   crypto/OS/Git/translator assumptions, not an unqualified "fully verified".

## D. Decisions deliberately excluded from first version

- Argon2id, scrypt and algorithm agility beyond one audited initial suite;
- arbitrary filename/path-bound AE without a reviewed rename story;
- authenticated freshness/rollback prevention without trusted external state;
- partial `git add -p` of protected plaintext files;
- modifying historical Git commits, rewriting remote history, or reliably
  erasing plaintext from backups;
- requiring the maintainer to accept a Python/Rust binary in the Bash
  installation path;
- adding a broad `--audit` UX despite prior maintainer preference for
  actionable initialization/migration warnings.

Each can be a future spec extension, not an excuse to loosen initial
interoperability or security gates.

## E. How to close a design decision

Record: date, chosen option, alternatives evaluated, security argument,
compatibility impact, corresponding spec revision, supported-host test
results, and (if relevant) maintainer and cryptography reviewer acceptance.
Changing a frozen decision requires a distinct on-disk format version where
serialized or cryptographic meaning changes; the existing version never
silently changes interpretation.
