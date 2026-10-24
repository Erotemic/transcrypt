# Transcrypt: interoperable Bash/Rust protocol and verification plan

**Status: secure-v3 planning proposal with partial implementation, 2026-10-24.**
The secure v3 protocol is not frozen or implemented in Bash or Rust, and
no Lean theorem has been compiled. There is now a separate released-v2
Rust envelope parser/serializer and legacy Bash hardening. Consult
[implementation progress](implementation-progress.md) for exact evidence
and limitations; this document does not promote a legacy result to a v3 proof.

## The intended result

One public, byte-exact, implementation-independent protocol specification;
two independently maintained and interoperable implementations; and one
machine-checked proof development about the Rust implementation's translated
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

| Document | Purpose | Type |
|---|---|---|
| [01 - Scope and adversary](01-requirements-and-threat-model.md) | Assets, attackers, required security properties, non-goals | Normative target |
| [02 - Protocol decisions](02-protocol-and-wire-format.md) | Inputs, public metadata, wire versioning, cryptographic design gate, byte-level spec checklist | Draft for approval |
| [03 - Git operation semantics](03-git-state-machine.md) | Clean/smudge, staged tree, init, unlock, rekey, migration, rollback, cache, worktrees | Normative target |
| [04 - Implementation layout](04-dual-implementation-architecture.md) | Bash crosswalk and Rust crate boundaries | Engineering plan |
| [05 - Verification](05-formal-verification.md) | Independent Lean spec, Aeneas extraction, theorem plan, trusted interfaces | Proof plan |
| [06 - Interoperability and CI](06-conformance-and-ci.md) | Exact acceptance matrices and required automation | Test plan |
| [07 - Audit closeout](07-audit-remediation.md) | Traceable disposition for every October 2026 audit finding | Remediation plan |
| [08 - Execution and PRs](08-roadmap-and-pr-plan.md) | Small incremental deliverables, dependencies, gates | Roadmap |
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

## First implementation gate

Close the **blocking** design decisions in
[10](10-decisions-and-blockers.md), publish a complete canonical format
specification and independent vectors, and have both the protocol reviewer
and the Bash-portability reviewer sign off. **Only then implement or revise
ciphertext serialization.** Safe remediation of independently specified
operational bugs (such as wrong-password rollback and symlinks) can proceed
before the cryptographic format is frozen.

### Current formal proof slice

- [Universal Base64 and policy proof evidence](reference/m6-formal-bitcore.md) (Z3 checked; Lean/Aeneas status explicitly tracked).
