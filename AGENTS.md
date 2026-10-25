# Working on Transcrypt v3

Read [the v3 product charter](docs/verification/V3-PRODUCT-CHARTER.md)
**before** proposing security hardening, formalization, changes to Git UX or
release gates. It is the current maintainer-directed statement of product
intent; older agent prompts and historical numbered roadmaps are not authority
for incompatible default behaviors.

- **Main promise:** user-selected files are authenticated ciphertext in public
  Git history. An unlocked local checkout behaves normally. Local-at-rest
  secrecy is not a default security guarantee.
- **Default UX (implemented):** arbitrary patterns via Git `.gitattributes`
  (`protect PATTERN` or `PATTERN transcrypt`), the derived key stored in
  `.git/transcrypt-v3/key` by `unlock`, and an optional `--private` mode
  (memory-only agent, 0600 plaintext). `migrate` converts Bash v2
  repositories. Check [the handoff](docs/verification/V3-HANDOFF.md) for the
  current state before changing any of it.
- **Keep real bugs in scope:** a plaintext staging bypass, wrong authentication
  context, attacker-controlled write, data loss or broken ordinary rename is
  not waived because a local privacy feature is optional.
- **Proofs:** preserve byte-exact v3 protocol and verified Rust-to-Lean
  correspondence. Named theorems about production-derived functions are
  distinct from adapter model proofs, Git/OS assumptions and crypto-library
  security. Do not introduce `sorry`, `admit` or weaken a spec to fit a bug.
  Normal development uses compilation; reserve transitive axiom inventory for
  the existing named audit milestones.
- **Version compatibility:** no legacy CBC/MD5 in the formally verified v3
  runtime. Provide explicit one-time v2-to-v3 migration; keep Bash semantic
  correspondence documented. Changes to authenticated wire semantics require
  a new profile/version rather than silent reinterpretation.
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
