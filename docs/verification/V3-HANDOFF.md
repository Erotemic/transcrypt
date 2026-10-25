# Transcrypt v3: durable handoff for the next contributor or agent

**Last reconciled:** 2026-10-25. **Branch:** `work/m2-nul-safe-path-enumeration`.
Always begin by checking the working tree and latest commits; this file is a
continuity aid, not a claim about later changes.

## Goal / anti-goals

Deliver the smallest secure-first Rust v3 lifecycle with meaningful
source-derived Lean refinement. V3 uses Argon2id and AES-256-CMAC-SIV,
canonical Git pathname authentication, one context and `*.secret` files.
Do not spend effort on legacy-v2 parity, Bash CLI porting, standalone SMT,
broad migration or full Git/OS formalization. Keep the independent spec
authoritative: Rust is changed to meet it, never the reverse.

## Where things are

| Concern | Canonical location |
| --- | --- |
| Roadmap, stage status, remaining work | `docs/verification/V3-ROADMAP.md` |
| Evidence per requirement | `docs/verification/V3-PROOF-COVERAGE.md` |
| Trust-ordered assumptions, adapter call-site table | `docs/verification/V3-ASSUMPTIONS.md` |
| Internal security review (V6) | `docs/verification/V3-SECURITY-REVIEW.md` |
| User documentation | `docs/verification/V3-USER-GUIDE.md` |
| Wire/AAD/Git behavior | `docs/verification/specs/V3-AUTHENTICATED-P0.md` |
| Verified pure core (codec + every decision) | `rust/crates/transcrypt-v3-core/src/lib.rs` |
| Crypto primitives (`Keyed: V3Primitives`), KDF | `rust/crates/transcrypt-v3/src/lib.rs` |
| Git adapter, agent, fd-relative FS | `rust/crates/transcrypt-v3/src/{main,session,fsat}.rs` |
| Independent Lean spec | `proofs/lean/Transcrypt/{V3Wire,V3WireCodec,V3Policy}.lean` |
| Generated Lean (do not edit) | `proofs/aeneas/v3/V3Wire/Extraction/` |
| Proofs | `proofs/aeneas/v3/V3Wire/Verification/{Copy,Codec,Bytes,Path,Protocol,Lifecycle}.lean` |
| Theorem ledger | `proofs/aeneas/v3/PROOF-STATUS.md` |
| Tests | `rust/crates/transcrypt-v3/tests/{git_lifecycle,adversarial,v3_vectors}.rs`, `tests/v3/reference/` |

## Verified state

- Every function of the core is translated by the pinned cargo-hax 0.4.2
  (Charon + Aeneas) toolchain and proved against the independent spec,
  covering full outputs, every error outcome and the absence of panics.
  Protocol theorems are relative to the explicit primitive contract
  `Realizes`. Lifecycle theorems are about Lean models of the adapter's
  loops.
- `bash proofs/aeneas/build-v3-tracked.sh` builds everything;
  `bash proofs/aeneas/check-v3-axioms.sh` shows only standard axioms.
- Rust: `cargo test --workspace` (lifecycle, adversarial, vectors, contract
  test). Python: `tests/v3/reference/*.py` need `cryptography>=42` (Ubuntu's
  41.x rejects empty AES-SIV plaintexts) and `argon2-cffi`; CI pins them.

## Commands

```bash
cd ~/code/transcrypt
cd rust && cargo test --workspace && cd ..
python3 tests/v3/reference/check_vectors.py -v      # in a venv with the pinned deps
python3 -m unittest discover -s proofs/aeneas/tests -p 'test_v3_*.py'
bash proofs/aeneas/build-v3-tracked.sh
bash proofs/aeneas/check-v3-axioms.sh
```

When the core changes: `bash proofs/aeneas/translate-v3-core.sh`, then
`python3 proofs/aeneas/v3_snapshot.py compare` (expected to fail), review
the regenerated `Funs.lean`, then run `refresh` and rebuild. Existing proofs
name generated loops (`*_loop0.body`, …); appending functions keeps them
stable, but reordering loops inside a proved function renames them.

## Proof engineering notes (hard-won)

- Generic whole-loop lemmas: `copy_loop` / `compare_loop` in `Copy.lean`
  (via `loop.spec_decr_nat`), and the pointwise `Copied` invariant.
- In loop bodies: `simp only [CoreModels.core.slice.Slice.len,
  CoreModels.rust_primitives.slice.slice_length]`, put length/constant facts
  and `have := usize_max_ge` in context **before** `step*`; it then
  discharges bounds and exit cases itself. Inspect leftovers with
  `trace_state`. Goal order after `step*` can surprise you.
- `rw` on dependent `getElem` indices fails; convert with `getElem!_pos`.
- `subst` on the result of a dependent `match` fails; rewrite the equation
  and `simp only [..., WP.spec_ok]`.
- Unnamed hypotheses: refer by type with `‹_›` instead of `rename_i` where
  possible.

## Next tasks (trust order)

1. Extract the `ls-files --stage -z` entry parser and agent frame parsing
   into the core and prove them (A4 reduction).
2. External review R-01.
3. Bash v7 only after a dependency-policy decision.

**Decision rule:** spend effort on proofs connected to shipped Rust or on
exploitable lifecycle failures, not on theorem counts.
