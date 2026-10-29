# Transcrypt: product vision, protocol and verification

**Status (2026-10-25):** the experimental Rust
v3 lifecycle exists; the Aeneas-extracted wire and decision core have
compiled refinement theorems, while the effectful Git/OS adapter and crypto
implementations remain explicitly assumed/tested rather than fully proved.
The [product charter](V3-PRODUCT-CHARTER.md) governs intended defaults and
non-goals. The [roadmap](V3-ROADMAP.md), [proof ledger]
(V3-PROOF-COVERAGE.md), [assumption register](V3-ASSUMPTIONS.md),
[security argument](V3-SECURITY-ARGUMENT.md) and
[handoff](V3-HANDOFF.md) track implementation and evidence. Historical
numbered documents describe earlier, potentially conflicting design choices.

**Current defaults:** files are selected by `.gitattributes` patterns, the
derived key is stored locally by `unlock` (with an optional memory-only
private mode), `git mv` is re-encrypted at commit, and `migrate` converts
Bash v2 repositories. The independent review's findings and their fixes
are in the [disposition](V3-REVIEW-TRIAGE.md).

## Secure-first v3 implementation (experimental)

The current implementation is an experimental [byte-exact v3 AES-SIV /
Argon2id candidate](specs/V3-AUTHENTICATED-P0.md) with Rust crates
`transcrypt-v3-core` and `transcrypt-rs`. Independent reference vectors and
real-Git tests accompany source-derived Lean refinements of the codec and
pure decision core. This is **not a formally verified executable or an
independently audited release**. The next product work is guided by the
[charter](V3-PRODUCT-CHARTER.md), not by repeating the narrow first proof
of concept or pursuing parity with legacy-v2 cryptography.

## The intended result

The *active* target is a highly usable Rust-first, byte-exact authenticated
protocol and a scoped machine-checked proof development. A future independent
Bash v3 implementation is desirable **if feasible without diluting security
or portability**, but is not a Rust-v3 release prerequisite. One-time
legacy-to-v3 migration is more important than legacy wire compatibility. The current
formalization is not blocked on writing the Bash v3 implementation. It uses a
public, implementation-independent specification and one machine-checked proof
development about the Rust implementation's translated
security-critical logic. The Bash implementation remains a standalone Bash +
OpenSSL product, with **no Rust or Python runtime dependency**. Correspondence
between Bash and the specification is established by human review and testing,
not by asserting that the Rust proofs also verify Bash.

```text
                    independently reviewed normative specification
                         /                    |                  \
                hand-reviewed                |                 Lean spec
                Bash + OpenSSL         Rust implementations             |
                         \           /         |                       |
                       common vectors   Charon -> Aeneas -> generated Lean
                              |                          |              |
                   interoperability tests     refinement theorems -------+
                              |
                Git state, migration, failures, portability tests
```

The independent specification, and not either implementation, defines the
observable behavior. A bug found in Bash is fixed in Bash; a bug found in the
Rust design is not promoted into the protocol simply to make proofs easy.

## Read in this order

For the current Rust-first work, read the product charter first. Consult the
original numbered plans for longer-term Bash interoperability, historical
audit findings, and source decisions.

| Document | Purpose | Type |
|---|---|---|
| [V3 product charter](V3-PRODUCT-CHARTER.md) | Normative intended UX, public-Git threat model, goals and non-goals | **Maintainer direction** |
| [Independent security review disposition](V3-REVIEW-TRIAGE.md) | Separate implementation bugs from legacy, optional local and deployment concerns | Active review triage |
| [Active v3 roadmap](V3-ROADMAP.md) | Current product milestones, statuses, proof evidence and next action | **Current plan** |
| [V3 proof coverage](V3-PROOF-COVERAGE.md) | Source-derived Lean theorems vs tests vs trusted assumptions | **Current status** |
| [V3 security argument](V3-SECURITY-ARGUMENT.md) | The end-to-end statement (selected paths enter Git as authenticated ciphertext) and every assumption it rests on | **Current status** |
| [V3 handoff](V3-HANDOFF.md) | Working branch, file map, commands, continuity rules | **Current handoff** |
| [01 - historical scope and adversary](01-requirements-and-threat-model.md) | Earlier requirements, including some superseded defaults | Historical reference |
| [02 - Protocol decisions](02-protocol-and-wire-format.md) | Inputs, public metadata, wire versioning, cryptographic design gate, byte-level spec checklist | Draft for approval |
| [03 - historical Git operation plan](03-git-state-machine.md) | Earlier clean/smudge, transaction and migration requirements | Historical reference; check charter |
| [04 - Implementation layout](04-dual-implementation-architecture.md) | Bash crosswalk and Rust crate boundaries | Engineering plan |
| [05 - Verification](05-formal-verification.md) | Independent Lean spec, Aeneas extraction, theorem plan, trusted interfaces | Proof plan |
| [06 - interoperability and CI](06-conformance-and-ci.md) | Earlier two-implementation acceptance matrix | Historical/test reference |
| [07 - Audit closeout](07-audit-remediation.md) | Traceable disposition for every October 2026 audit finding | Remediation plan |
| [08 - Execution and PRs](08-roadmap-and-pr-plan.md) | Historical full Bash/Rust/upstream program, dependencies and gates | Long-range plan (superseded for active Rust v3) |
| [09 - Hand review](09-bash-traceability-and-review.md) | Hand-auditable mapping and change-review checklist | Review procedure |
| [10 - Decisions](10-decisions-and-blockers.md) | Accepted requirements vs proposed choices vs mandatory unresolved design decisions | Decision register |
| [Reference: current candidate](reference/current-candidate.md) | Descriptive account of the **unreleased** October 2026 `TCRYPT3` prototype | Non-normative evidence |
| [Reference: released v2 bytes](reference/v2-wire-structure.md) | Legacy cipher-independent envelope parser/serializer contract and next proof target | Legacy reference |
| [Implementation progress](implementation-progress.md) | Implemented slices and build/test evidence, remaining blockers | Execution log |
| [Reference: sources](reference/sources.md) | Maintainer discussions, standards, tooling, source baselines | Evidence register |

## Versions and source provenance

- **Legacy v2:** current shipping-compatible Transcrypt behavior and its Git
  history. Reads stay supported; existing repositories must not silently
  change their encryption representation.
- **Upstream v3 integration baseline:** `elasticdog/transcrypt-v3` at
  `fcf94da40f31110122577b857a1102ff4a486cf3` (PR #219, draft).
  At that commit, PBKDF2 is **not implemented**: the committed settings reader
  accepts only legacy values, and the split v2/v3 Bats suites are groundwork.
- **Unreleased proof-of-concept:** `transcrypt-v3-authenticated-pbkdf2-final-overlay.tar.gz`
  from the October 2026 development conversation. It adds `TCRYPT3:` records
  and PBKDF2 but has verified security defects (see [07](07-audit-remediation.md)).
  It is an inspection and vector source, **not the normative secure format**.
- **Earlier prototype:** `alternative-enhancement` at `76f00e1`, useful only
  for design history and regression vectors, not a merge source.

The initial planning overlay was documentation-only. Subsequent development
commits added legacy Bash safety fixes, feasibility probes, and a zero-dependency
Rust v2 envelope crate. Those implementation changes are distinct from the
**unreleased** `TCRYPT3` prototype and do not finalize a secure v3 format.

## Project rules

The [maintainer charter](V3-PRODUCT-CHARTER.md) takes precedence over older
product scope and agent stopping criteria. Rules below about Bash release
process and two-way interoperability govern that *later* independent track,
not the Rust v3 product's default UX or one-time transition requirement.


1. Specify externally observable success **and failure** behavior first.
2. Treat format versions as immutable after release. An incompatible change
   requires a distinct discriminator; never silently reinterpret ciphertext.
3. Keep cryptographic security analysis separate from functional correctness.
4. Prove Rust against the independent model, not Rust against a copied Rust
   implementation or a test oracle derived solely from Bash.
5. Reuse one canonical set of public test vectors in both implementations;
   independently recompute standards-based cryptographic vectors.
6. Every proof claim names exactly which extracted functions and trusted
   external operations it covers.
7. Every Bash correspondence claim includes a source revision, reviewer,
   requirement IDs, and tests; code changes invalidate affected reviews.
8. Legacy behavior is tested throughout the project. Migration is always
   explicit and recoverable; it does not erase historical cryptographic risks.
9. Do not ship a new format or upgrade defaults until the security and
   portability gates in [08](08-roadmap-and-pr-plan.md) are satisfied.
10. Preserve the maintainer's small-PR workflow and do not require the
    maintainer to operate a Rust/Lean toolchain to release the Bash tool.

## What we can eventually claim

- **Bash**: conforms to the documented byte protocol under reviewed code
  assumptions and the tested platform matrix; this remains manual/test
  assurance, not full formal verification.
- **Rust core**: selected Rust functions are translated using Charon/Aeneas
  and their behavior is proved equivalent to an independently defined Lean
  specification, modulo explicitly named opaque primitives and translation
  assumptions.
- **Full Git CLI**: stronger end-to-end claims require the Git, filesystem,
  process, and credential adapters to be verified or their contracts to be
  validated separately. A theorem about a pure parser does not establish
  transactional migration or local secret confidentiality.
- **Cryptography**: confidentiality/authenticity claims rely on a chosen,
  externally reviewed construction and stated computational assumptions;
  an Aeneas functional-refinement proof does not establish those claims.

## Historical first implementation gate (superseded for active Rust v3)

For the original Bash-inclusive integration campaign, close the **blocking** design decisions in
[10](10-decisions-and-blockers.md), publish a complete canonical format
specification and independent vectors, and have both the protocol reviewer
and the Bash-portability reviewer sign off. **Only then implement or revise
ciphertext serialization.** Safe remediation of independently specified
operational bugs (such as wrong-password rollback and symlinks) can proceed
before the cryptographic format is frozen.

### Current formal proof slice

- [Universal Base64 and policy proof evidence](reference/m6-formal-bitcore.md) (Z3 checked; Lean/Aeneas status explicitly tracked).

### Executable Rust/Bash parity milestone

The first implemented cross-language filter boundary is the released **legacy
v2 format**, specified in [the byte-exact v2 contract](specs/LEGACY-V2-INTEROPERABILITY.md).
`rust-legacy/crates/transcrypt-legacy` is an actual Rust `clean` / `smudge` /
`textconv` implementation for Bash-initialized repos, while
`rust-legacy/crates/transcrypt-legacy-core` contains its pure Aeneas-targeted
functions. This is *not* the final authenticated v3 suite. The current Rust-first remaining work is in `V3-ROADMAP.md`; the full
Bash/upstream roadmap remains in `08-roadmap-and-pr-plan.md`. Generated Lean
source and three narrow correspondence theorems have compiled; full codec
functional refinement remains open.
