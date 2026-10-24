# Transcrypt v3: durable handoff for the next contributor or agent

**Last reconciled:** 2026-10-24, after the path-bound v3 Rust compilation fix.
**Branch:** `work/m2-nul-safe-path-enumeration` (user reported the tracked
Aeneas foundation pushed to this branch and the subsequent compile fix works).
Always begin by checking the actual working tree and the latest commits;
this file is a continuity aid, not a claim to have inspected future changes.

## Goal / anti-goals

Deliver the **smallest secure-first Rust v3 lifecycle with meaningful
source-derived Lean refinement**. V3 uses Argon2id and AES-256-CMAC-SIV,
canonical Git pathname authentication, one context and `*.secret` files.
Do not spend the next round on legacy-v2 parity, Bash CLI porting, more
standalone SMT, broad migration, proof-certificate mechanics, or full Git/OS
formalization. Keep the independent byte spec authoritative.

## Key entrypoints

| Concern | Canonical code or document |
| --- | --- |
| Active milestones and stop conditions | `docs/verification/V3-ROADMAP.md` |
| Verification obligations and status | `docs/verification/V3-PROOF-COVERAGE.md` |
| Precise v3 wire/AAD/Git behavior | `docs/verification/specs/V3-AUTHENTICATED-P0.md` |
| Actual pure Rust codec | `rust/crates/transcrypt-v3-core/src/lib.rs` |
| Actual encrypted adapter and Git lifecycle | `rust/crates/transcrypt-v3/src/{lib,main,session}.rs` |
| Independent Lean codec model | `proofs/lean/Transcrypt/{V3Wire,V3WireCodec}.lean` |
| Tracked generated Rust semantics | `proofs/aeneas/v3/V3Wire/Extraction/Funs.lean` |
| Current real-source correspondence theorems | `proofs/aeneas/v3/V3Wire/Verification/Refinement.lean` |
| Source hash and translator pins | `proofs/aeneas/v3/SNAPSHOT.json` |
| Snapshot/update procedure | `proofs/aeneas/v3/README.md` |
| Git/adversarial tests | `rust/crates/transcrypt-v3/tests/` |
| Independent crypto/path vectors | `tests/v3/reference/` |
| CI | `.github/workflows/run-bats-core-tests.yml` |

## Verified current state and gaps

- The user confirmed the Rust build/tests and latest path-bound compile fix
  work; do not downgrade that to "unreported" absent contrary evidence.
- The tracked Aeneas-generated Lean code matches the Rust codec source and
  the imported magic/version correspondence theorems compile. Snapshot
  consistency is checked in CI.
- The four generated codec operations exist, but **full-field functional
  refinement of their RustM loops is open**. No theorem currently establishes
  the entire live authenticated Git lifecycle.
- The AES-SIV library, KDF, entropy, filesystem, socket and Git operations
  remain external security/functional assumptions. This is an experimental
  prototype, not a production-safe secret store.

## Immediate next task (vertical proof step)

Prove **`encode_file_header`** against the independent 22-byte header
serializer using the actual generated function. Begin by reading the function
and its two generated loops in `V3Wire/Extraction/Funs.lean`. Determine its
`RustM` success representation and exact array-to-list projection. Build a
small theorem that returns all bytes (including arbitrary 16-byte config ID),
then generalize reusable array-loop lemmas for config encoding and decoders.

A proof only about `FILE_MAGIC`, reflexivity, a manually written copy of the
Rust function, or unconnected SMT models does not complete the task. If
Aeneas loop structure causes avoidable proof debt, refactor the **production
Rust** byte-copy loop to an Aeneas-friendly safe expression and regenerate
before proving; preserve canonical Rust/vector/Git tests and public bytes.

Run normally:

```bash
cd ~/code/transcrypt
cd rust && cargo test --offline --workspace && cd ..
python3 tests/v3/reference/check_vectors.py -v
python3 proofs/aeneas/v3_snapshot.py verify
bash proofs/aeneas/build-v3-tracked.sh
```

If the Rust core changes, run the pinned translator, inspect the diff,
compare then explicitly refresh the snapshot as described in
`proofs/aeneas/v3/README.md`. Avoid regenerating for proof-only edits.

## Update protocol for each merged step

1. Land actual code and/or a theorem, with the ordinary focused build gate.
2. Add a row or update the evidence in `V3-PROOF-COVERAGE.md`, including
   accepted assumptions; update the short status note in
   `proofs/aeneas/v3/PROOF-STATUS.md` if the proof boundary moved.
3. Mark one milestone acceptance item in `V3-ROADMAP.md`; add a **dated,
   append-only** note to `implementation-progress.md` for why the milestone
   moved, not another full replacement roadmap.
4. If an incompatible experimental cryptographic profile is changed,
   update the independent spec, vectors, Git tests and compatibility note;
   do not silently reinterpret ciphertext under a public released marker.
5. Keep artifacts limited to destination paths in a single ZIP overlay; use
   normal tests, then exact `git add` and one `git commit` with attribution.

**Decision rule:** spend effort on meaningful proofs connected to shipped
Rust or exploitable lifecycle failures, not on increasing theorem counts.
