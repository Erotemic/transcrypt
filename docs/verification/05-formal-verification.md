# 05. Machine-checked Rust refinement and assurance boundaries

**This is a proof plan, not proof output.** The goal is a line of evidence
from independently written mathematical definitions to **actual Rust source**,
not to an independent handwritten Rust-like Lean reimplementation.

## 1. The verification chain

```text
Independent normative protocol + state-machine specification
         |
         v
Lean Spec/ : definitions, properties, external operation contracts
         ^                         ^
         | refinement proofs       | abstract crypto/Git contracts
         |
Lean Generated/ : translation of named, released Rust crate functions
         ^
         | Charon + Aeneas (version pinned; reproducibly regenerated)
         |
Rust protocol-policy crate source -> rustc -> compiled distribution
```

Aeneas translates a supported *safe Rust* subset via Charon's LLBC to a
functional theorem-prover representation. The current Aeneas documentation
lists limitations including some loops, closures, interior mutability,
concurrency and certain borrow signatures; these must be tested in the
selected toolchain, not assumed away. See [sources](reference/sources.md).

Only the functions actually present in the generated Lean code, at the
recorded Rust commit, enter refinement theorems. A manually written Lean
function can help explain the spec but **cannot by itself prove any Rust
function correct**.

## 2. Independent Lean specification

Model pure objects and transitions with opaque idealized crypto operations:

```text
Bytes
ContextId
Config
FormatVersion
Record
Operation
Result Error A
StageSnapshot
RepoModel
TransactionPlan

seal_spec : Keys -> AssociatedData -> Bytes -> Bytes
open_spec : Keys -> AssociatedData -> Bytes -> Except Error Bytes
parse_config_spec : Bytes -> Except Error Config
parse_record_spec : Bytes -> Except Error Record
plan_migration_spec : RepoModel -> Request -> Except Error TransactionPlan
check_stage_spec : StageSnapshot -> Except Error Unit
```

The signatures above are mathematical sketches, not executable Lean declarations.
Use independent, non-Rust-shaped definitions: byte grammar, decoding
predicates, finite maps of paths to blobs, and explicit pre/postconditions.
Prove the reference spec is **internally consistent** before refinement.

The model must separate:

- Static format properties (lengths, bounds, canonicalization);
- Crypto API assumptions (correctness and authenticity);
- Git state invariants (protected files, staged metadata, contexts);
- OS effects (atomicity, visibility, error propagation);
- Information released to stdout, files, process args, logs and Git objects.

## 3. Initial theorem suite and evidence level

| ID | Candidate theorem / obligation | Formal level | External assumptions |
|---|---|---|---|
| T-01 | `parse(serialize(r)) = Ok(r)` for every well-formed record | Pure Lean + translated parser | None beyond representation semantics |
| T-02 | Accepted encodings are canonical; malformed/ambiguous/noncanonical encodings are rejected | Pure Lean + translated parser | None, except bounded allocation contract for input I/O |
| T-03 | Public-config parsing does not silently fill mandatory secure fields or accept conflicting duplicates | Pure Lean + translated parser | None |
| T-04 | Format dispatch is disjoint: invalid secure ciphertext cannot reach legacy decoder | Pure policy function | None for dispatch; CLI connection separately reviewed |
| T-05 | Under the crypto `open(seal(p)) = p` law, Rust `seal/open` composition returns the same bytes and context | Conditional protocol theorem | Crypto correctness law |
| T-06 | Under crypto authenticity, all failed authentication paths release zero plaintext | Pure buffer-output contract + effects | Cryptographic unforgeability and no-early-write I/O adapter |
| T-07 | `check_stage = Ok` implies complete matching public config for all protected secure blobs in supplied staged snapshot | Pure staged-tree model and policy crate | Correct Git snapshot adapter |
| T-08 | Changing effective crypto metadata without transforming affected blobs cannot pass `check_stage` | Pure model | Correct authenticated validation primitive |
| T-09 | Failed `plan_unlock` or `plan_migration` emits no write effects | Pure planner refinement | Adapter only executes accepted plans |
| T-10 | Successful `plan_migration` preserves path/context/plaintext mapping, given valid old decrypt and new seal | State transition refinement | Crypto and Git index effects |
| T-11 | Rekey selects fresh public salt by default and never preserves old encryption keys in the proposed transition | Planner theorem | RNG freshness/execution and adapters |
| T-12 | Parser and planners terminate, avoid overflow, and are total over bounded input domains | Pure Rust/Aeneas proof | Translation semantics and parser input bound |
| T-13 | For the model's secure emitter, no successful protected-path stage event contains raw plaintext | Trace/state theorem | Correct Git clean/filter adapter; remote bypass excluded |
| T-14 | A wrong credential does not cause a persistent-state change when the concrete adapter implements preflight + rollback contract | Refinement of effect specification | Filesystem atomicity/rollback implementation |
| T-15 | A record from a different context/suite/config cannot be authenticated by the wrong associated data except per crypto security assumptions | Conditional crypto theorem | Authenticated-encryption/PRF guarantees |

**Order:** prove T-01..T-04, T-12 first; T-07..T-09 next; then
crypto-compositional T-05..T-06/T-15; finally Git/effect T-10/T-13/T-14.
A theorem name existing in a file does not count as complete: it must be
proved about the **generated function(s)** for the pinned Rust revision.

## 4. Aeneas execution plan

1. Pin Rust compiler, Charon, Aeneas, their Lean backend, Lean 4, and mathlib
   revisions as needed. Check backend compatibility first. Keep the pin
   manifest in proof repository version control.
2. Start with a tiny safe Rust parser/decision-kernel crate; no external
   crates or I/O in the first extraction slice, no `unsafe`.
3. Produce `.llbc` from the *actual Rust crate* with
   `charon cargo --preset=aeneas --dest-file=proofs/generated/policy.llbc`
   from the Rust proof-kernel crate; translate `policy.llbc` to Lean
   using the matching pinned Aeneas backend. The exact build script is a
   later deliverable once the Rust crate and toolchain have been pinned.
4. Check in or reproducibly regenerate a **generated source manifest** that
   records source SHA, tool SHAs, exposed functions and any `opaque` items.
5. Supply Lean definitions/contracts for every opaque external used by the
   generated functions; flag any unproved axiom-like assumptions in the
   human-reviewed assurance ledger.
6. Implement refinement proofs against the independent `Spec/` definitions.
7. A CI gate regenerates the translation from pinned Rust source and verifies
   no unreviewed drift; then compiles the focused Lean modules. `lake exe
   cache get` is run before `lake build` where mathlib is used.
8. Later modules widen from parsing to planning, then external Git effects
   through explicit contracts. Proof source and application code stay
   separately reviewable.

Avoid unsupported translation patterns in the proof kernel. If a core
function cannot be translated, refactor the real Rust implementation or
choose an appropriate verification method; do not claim that verifying a
handwritten lookalike is the same result.

## 5. What is inside and outside the trusted computing base?

| Component | Initially trusted / proved? | How to reduce risk |
|---|---|---|
| Lean kernel and checked theorem statements | Trusted checker, proof terms checked | Pin version, build focused theorem targets |
| Charon/Aeneas translation correspondence to compiled Rust | Trusted or separately justified translation chain | Pin revisions, generate exact code, execute cross-checks, review translation assumptions |
| Rust compiler/backend and deployed binary | Trusted compilation chain | Reproducible builds, toolchain provenance, optional diverse compilers |
| Pure Rust parsers/decision planners | **Prove** via generated functions | T-01..T-04, T-07..T-12 |
| AES/SIV, PBKDF2, HMAC implementations | Initially **trusted crypto primitives** | Standards vectors, independent library review, optional deeper primitive proofs |
| RNG | Trusted entropy source | Test deterministic fixture injection separately; OS entropy assumptions |
| Git index/attributes/objects, syscall semantics | Trusted concrete adapter operations | Contracts, adversarial integration tests, fault injection, optional Verus/Kani/other method |
| Secret input, TTY, environment, argv, key storage | Trusted OS-facing CLI | Process/runtime audits, keep secret-bearing ops small |
| Bash/OpenSSL implementation | **Not formally proved by Aeneas** | Function-by-function manual mapping and independent differential tests |
| Native code dependencies and supply chain | Trusted packaging/dependencies | Pin dependencies, audit, SBOM, signed provenance |

Aeneas establishes functional properties of translatable Rust code under its
translation model. It does **not** automatically prove computational
cryptographic security, memory erasure, absence of timing side channels, or
all effects of Git/process commands. Those claims need separate evidence.

## 6. Alternative tools as supplements, not proof substitution

- **Kani:** bounded model checks / counterexamples for parser overflows,
  panics, truncated buffers and selected unsafe adapters. Loops may be
  bounded; record the harness and bound.
- **Verus or Creusot:** possible verification of effect-aware or
  unsupported-by-Aeneas Rust functions with explicit specifications. Keep
  proof coverage distinct and do not imply a unified theorem where none
  exists.
- **Property-based fuzzing:** malicious config/record/path corpora and
  concrete code coverage. Powerful bug detection, not universal proof.
- **Bash correspondence:** human review and differential tests. No theorem
  about Bash until an actual Bash semantics/extraction/refinement project
  is separately undertaken.

## 7. Proof acceptance per milestone

For each proved function, evidence consists of:

1. SHA of actual Rust source and exact function symbol;
2. Charon/Aeneas/toolchain pins and reproducible generation steps;
3. independently stated spec and theorem statement;
4. compiled Lean module containing proof about the generated function;
5. explicit opaque items/assumptions and their contracts;
6. corresponding running Rust tests and Bash/Rust conformance vectors;
7. a concise coverage map stating which requirement IDs are now machine
   checked and which remain merely tested/reviewed.

Routine Lean proof development uses focused `lake build` and normal compiler
diagnostics; it does not require bulk `#print axioms` dumps or repetitive
`#check` logging. A separate, named final transitive-assumptions audit may
compare against a reviewed baseline before a formal release claim.
