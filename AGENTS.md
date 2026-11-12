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

## Profiles and the portable Bash client (2026-11-11)

The committed config's byte 6 is the **profile** (1 Argon2id, 2 scrypt,
3 PBKDF2); records are `TV3F 00 01` for every profile. The verified core
decides the key derivation (`profile_kdf`, `derive_config_key`;
`Profiles.lean`). `contrib/v3/transcrypt-bash` implements profiles 2 and 3
byte-for-byte like Rust (config, records, `.git/transcrypt-v3/key`) and the
shared Git workflows. When changing either client run
`bash tests/v3/bash/test_reference.sh` and
`bash tests/v3/conformance/run.sh` (needs `cargo build --release`); keep the
Bash script `scripts/lint-shell.sh` clean (shfmt reformats associative
array keys containing `/` as arithmetic: quote them). Bash has empirical
evidence only (A27), never Lean theorems. Spec:
`docs/verification/specs/V3-PORTABLE-PROFILES.md`; parity matrix in the
dual-implementation roadmap. Do not add local-process isolation obligations
to the Bash path; prioritize authenticated Git publication and recovery.
