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
| Proofs | `proofs/aeneas/v3/V3Wire/Verification/{Copy,Codec,Bytes,Path,Index,Frame,Protocol,Lifecycle}.lean` |
| Theorem ledger | `proofs/aeneas/v3/PROOF-STATUS.md` |
| Tests | `rust/crates/transcrypt-v3/tests/{git_lifecycle,adversarial,v3_vectors,v3_differential}.rs`, `tests/v3/reference/` (`differential.py` regenerates the OpenSSL/argon2 corpus) |

## Verified state

- Every function of the core is translated by the pinned cargo-hax 0.4.2
  (Charon + Aeneas) toolchain and proved against the independent spec,
  covering full outputs, every error outcome and the absence of panics.
  Protocol theorems are relative to the explicit primitive contract
  `Realizes`. Lifecycle theorems are about Lean models of the adapter's
  loops.
- `bash proofs/aeneas/build-v3-tracked.sh` builds everything;
  `bash proofs/aeneas/check-v3-axioms.sh` shows only standard axioms.
- Rust: `cargo test --workspace` (lifecycle, adversarial incl. SIGKILL fault
  injection, vectors, differential, contract test). Python:
  `tests/v3/reference/*.py` need `cryptography>=42` (Ubuntu's 41.x rejects
  empty AES-SIV plaintexts) and `argon2-cffi`; CI pins them.

## Commands

```bash
cd ~/code/transcrypt
cd rust && cargo test --workspace && cd ..
python3 tests/v3/reference/check_vectors.py -v      # in a venv with the pinned deps
python3 tests/v3/reference/differential.py          # same venv
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

## Adapter invariants (do not regress)

These came out of the hardening campaign (`V3-SECURITY-REVIEW.md` §5); each
has a regression test in `tests/adversarial.rs`.

- Read Git objects only by object id, from one parsed snapshot, through
  `git_blob` (one shared `cat-file --batch` with exact reply framing,
  bounded). Never use `:<path>` revision syntax.
- Create Git subprocesses only with `git_command` (literal pathspecs, no
  replace refs). Never `git add -- <path>` with repository-derived paths;
  re-index with `update-index -z --stdin`.
- Replace a worktree file only through `Protected::replace` with the stamp
  from the read that justified it, while holding `staging_dir` (its
  `flock`).
- Release plaintext only through the agent's `open_record`. While locked,
  filters may only pass through inputs accepted by `record_envelope_ok`.
- Smudge may emit plaintext only when `umask_is_private()`; otherwise Git
  must receive the (authenticated) record. Plaintext files are otherwise
  written only by `hydrate` (0600).
- `hydrate` replaces only files that are authentic records for their path,
  and re-indexes only files holding the staged plaintext.
- Run every subprocess through `run_bounded` (directly or via `git`,
  `git_with_input`, `output`); never `Command::output()`.

## Next tasks

See the ranked list in `V3-ROADMAP.md` ("Remaining"). In short:
server-side `audit` deployment (A13; `contrib/v3/pre-receive`), external
review R-01, then the A4
remainder (prove the `cat-file --batch` header check; long-running filter
protocol for speed).

**Decision rule:** spend effort on proofs connected to shipped Rust or on
exploitable lifecycle failures, not on theorem counts.
