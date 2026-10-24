# 08. Phased delivery, dependencies, and upstream PR strategy

**Upstream workflow:** small reviewable PRs against `transcrypt-v3`, as
requested by the maintainer in [issue #134](https://github.com/elasticdog/transcrypt/issues/134#issuecomment-4478657672).
PR #219 remains the existing draft integration container, not a request to
merge the whole final Rust/formalization development as one change.

The first two upstream steps already exist: reading non-secret public config
(PR #210) and splitting Bats tests (PR #211). Preserve them as groundwork.
Documentation changes do not claim to complete step 3 (PBKDF2).

## Milestones and non-negotiable gates

| Stage | Deliverable | Dependencies | Definition of done | Intended upstream boundary |
|---|---|---|---|---|
| M0 | This complete planning/specification package | PR #219 snapshot, audit, maintainer discussions | Docs accepted for discussion; open blockers named; no code changed | Docs-only PR |
| M1 | Freeze canonical secure format and independent vectors | D-01..D-06 decisions; Bash capability prototype | Exact byte grammar, deterministic AE decision, KDF transcript, context/metadata semantics, vector provenance, two reviewers | Spec + vectors PR |
| M2 | Fix Bash operational defects independent of crypto format | R-10..R-18 state machine | Repro tests A1,A2,A4,A5,A7,A8 pass with no v2 regression; staged metadata and rollback actually checked | One or more narrow Bash hardening PRs |
| M3 | Implement secure Bash crypto primitives for M1 | M1, successful no-secret-argv design | Complete authenticated clean/smudge, strict parsing, no key argv, v3 Bats, supported platform tests | Encryption + tests PR(s) |
| M4 | Add public-config initialization, CLI and safe persistence | M1..M3 | Fresh repos/classified correctly, opt-in credential handling, public config available to clones | Init/config PR |
| M5 | Build migration and rekey transactions | M2..M4 | Two+ contexts, dirty worktrees, wrong password, cache inventory, recovery and clone invariants pass | Migration then hardening PR(s) |
| M6 | Implement independent Rust protocol/parser and interop | M1 | Rust compiles; exact vectors and 2-way Bash interop pass; no secret argv | Optional Rust source/distribution PR or separate repo |
| M7 | Translate real Rust core via Charon/Aeneas | M6, pinned toolchain | Generated Lean built from exact Rust SHA; opaque contracts enumerated | Proof/toolchain PR in Rust project |
| M8 | Prove parser and policy refinement | M7, Lean independent spec | T-01..T-04, T-07..T-09, T-12 compiled about generated code | Narrow theorem PRs |
| M9 | Connect CLI/Git effect contracts and prove selected transitions | M5,M8 | T-05..T-06,T-10..T-11,T-13..T-15 with explicit assumptions; fault tests | Proof/adapter PRs |
| M10 | Security review and both distribution releases | M3..M9 relevant release gates | No open release blockers; review of algorithm, tested platform matrix, matching docs/packaging | Final integration and separate releases |

M2 and M6 can partially proceed in parallel after the relevant spec slice is
agreed. No premature `TCRYPT3` wire freeze or claim of a fully verified Git
CLI. Bash need not wait for all M9 proofs to ship *legacy bugfixes*, but a
new "formally verified Rust release" claim requires explicit proof coverage.

## Suggested small code-PR split (after M0/M1)

1. **Safe path and metadata preflight**: reject symlinks/missing config;
   distinguish staged vs worktree config; normal repo classification.
2. **Staged ciphertext validator**: strict authenticated record check and
   byte-safe path enumeration; no magic-only acceptance.
3. **Transactional wrong-password handling**: preauthenticate; rollback
   filters/local credentials; error-output contract.
4. **Final cryptographic algorithm**: small independently reviewable
   implementation with KDF/format vectors and no argv-secret route.
5. **v3 Bats coverage**: contexts, empty/binary files, malformed data,
   cross-host compatibility, test vector promotion.
6. **Versioned config initialization**: canonical metadata generation,
   capability selection and user-visible diagnostics.
7. **Migration/rekey**: temp index, complete re-encryption, notes inventory,
   recovery/error injections.
8. **Rust implementation**: kept optional to upstream; equivalent format
   parser, policy, crypto, CLI and Git adapters by feature slice.
9. **Proofs**: independent model, generated source, then theorem milestones.

Avoid bundling GPG, partial staging, rename tracking, or Argon2id with the
first secure-format PR merely because they are interesting. Track optional
improvements separately so security review is tractable.

## Acceptance checkpoints before changing implementation

### Gate A: requirements approved

- [ ] Maintainer agrees with format/version and required new-format failure
      semantics, or a documented contributor-owned fork policy is selected.
- [ ] Security reviewer agrees with adversary model and allowed leakage.
- [ ] No requirement accidentally assumes Git hooks enforce server policy.

### Gate B: crypto and Bash feasibility

- [ ] Chosen deterministic authenticated algorithm has a specific published
      construction/security definition or an independent crypto review.
- [ ] Bash/OpenSSL implementation feasibility tested on real supported
      OpenSSL/LibreSSL versions with **no extra runtime** and no keys in argv.
- [ ] Rust implementation can use an audited in-process library with the
      same agreed wire bytes.
- [ ] Effective salt length, KDF parameters, key separation, authenticated
      associated data, and config commitment are fixed, not placeholders.
- [ ] Wire discriminator cannot be confused with the unreleased prototype.

### Gate C: operational correctness

- [ ] All known audit regressions close with reproducible tests.
- [ ] v2 tests stay green; v3 tests truly exercise v3.
- [ ] New config + every encrypted staged file form one decryptable tree.
- [ ] Wrong password, faults, and cancellation leave a recoverable state.
- [ ] Migration succeeds on named contexts and handles caches honestly.
- [ ] Clone/rebase/merge across supported OpenSSL/LibreSSL versions works.

### Gate D: formal assurance

- [ ] Rust toolchain/Aeneas version pins are checked in.
- [ ] Generated Lean source is demonstrably derived from the released Rust
      functions and matches pinned hashes.
- [ ] Independent Lean specification is not copied from generated code.
- [ ] Focused Lean builds succeed for claimed theorems.
- [ ] Crypto/OS/Git and translator assumptions are identified, with each
      assurance claim no stronger than its verified scope.

### Gate E: distribution

- [ ] Bash remains independently installable with original dependency policy.
- [ ] Rust executable is opt-in, independently versioned/distributed and
      interoperable with Bash within advertised support matrix.
- [ ] Migration documentation warns of historical and cached exposures.
- [ ] A security reviewer signs off on modern cipher/KDF use and known
      residual risks before the first security-branded release.

## First coding task after this planning overlay

M1: choose/prototype an interoperable deterministic authenticated encryption
scheme with no Bash-added dependency and safe secret handling, then write the
final format document and vectors. M2 operational hardening that does not
alter format bytes can occur independently. The existence of previous Rust
prototype source does not skip M1 or the initial translation/compilation
proof gates.
