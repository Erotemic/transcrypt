# Working on Transcrypt v3

Read [the v3 product charter](docs/verification/V3-PRODUCT-CHARTER.md)
and the [dual-implementation roadmap](docs/verification/V3-DUAL-IMPLEMENTATION-ROADMAP.md)
**before** proposing security hardening, formalization, changes to Git UX or
release gates. It is the current maintainer-directed statement of product
intent; older agent prompts and historical numbered roadmaps are not authority
for incompatible default behaviors.

- **Main promise:** user-selected files are authenticated ciphertext in public
  Git history. An unlocked local checkout behaves normally. Local-at-rest
  secrecy is not a default security guarantee. The primary adversary is an
  offline reader of public Git, not a process on the trusted developer host.
  Derived keys in local Bash/OpenSSL process arguments are an accepted
  portability tradeoff, not a release-blocking vulnerability by themselves.
  Secrets accidentally published to Git remain critical defects.
- **Default UX (implemented):** arbitrary patterns via Git `.gitattributes`
  (`protect PATTERN` or `PATTERN transcrypt`), the derived key stored in
  `.git/transcrypt-v3/key` by `unlock`, and an optional `--private` mode
  (memory-only agent, 0600 plaintext). `migrate` converts Bash v2
  repositories. Check [the handoff](docs/verification/V3-HANDOFF.md) for the
  current state before changing any of it.
- **Keep real bugs in scope:** a plaintext staging bypass, wrong authentication
  context, attacker-controlled write, data loss or broken ordinary rename is
  not waived because a local privacy feature is optional.
- **Proofs:** prioritize human-consequential publication, authentication,
  cross-profile rejection and data-recovery claims; Bash corresponds through
  empirical tests, not inherited Lean theorems. Preserve byte-exact v3
  protocol and verified Rust-to-Lean correspondence. Named theorems about production-derived functions are
  distinct from adapter model proofs, Git/OS assumptions and crypto-library
  security. Do not introduce `sorry`, `admit` or weaken a spec to fit a bug.
  Normal development uses compilation; reserve transitive axiom inventory for
  the existing named audit milestones.
- **Version compatibility:** no legacy CBC/MD5 in the formally verified v3
  runtime. Preserve existing Rust Argon2id/AES-SIV profile 1 and all of its
  guarantees. Add portable, separately versioned AES-SIV profiles for Bash +
  OpenSSL 3.0.13 and Rust; inspect committed config and fail clearly when a
  backend does not support its profile. No automatic crypto downgrade.
  Provide explicit one-time v2-to-v3 migration and profile conversion.
  The target is empirical Bash/Rust Git feature parity on shared profiles,
  with stricter local hardening remaining available in Rust.
- **Work order:** actual consequential defects, arbitrary protected-file
  selection, transparent persistent unlock, routine Git workflows, conditional
  formal coverage, migration, simplicity/portability/performance. Rerank
  based on evidence; after each task, seek the next meaningful improvement.
- **Evidence and continuity:** update the roadmap, proof ledger, assumption
  register and handoff for material changes. Run relevant Rust/Git tests and
  Lean builds when modifying proved code. Report what ran; no unverified
  success claims or documentation claiming its own contract was followed.
- **Review triage:** read
  [the independent review disposition](docs/verification/V3-REVIEW-TRIAGE.md).
  Distinguish in-scope Rust defects from v2 history, optional local privacy,
  and deployment-dependent guarantees.

The maintainer's current product direction controls what *should* be built;
actual code and executed evidence control claims about what *is* built.

## Portable Bash reference implementation (2026-11-11)

`contrib/v3/transcrypt-bash` now implements **profile 2** with a separately
versioned scrypt/AES-SIV protocol; keep profile 1 byte-exact and Rust-only
on OpenSSL 3.0. `tests/v3/bash/test_reference.sh` checks independent fixed
byte vectors and a real-Git lifecycle. Run it when changing the Bash
backend. This is a partial implementation of the dual-implementation
roadmap, **not** evidence of Rust/Bash parity or a completed Lean proof.
Do not add local-process isolation obligations merely to make the Bash path
look like Rust; prioritize authenticated Git publication and recovery.
