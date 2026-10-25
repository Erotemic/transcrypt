# Transcrypt v3: durable handoff for the next contributor or agent

**Last reconciled:** 2026-10-25 (after the third hardening pass, H-16 to H-27). **Branch:** `work/m2-nul-safe-path-enumeration`.
Always begin by checking the working tree and latest commits; this file is a
continuity aid, not a claim about later changes.

## Product direction vs current implementation

**Read [V3-PRODUCT-CHARTER](V3-PRODUCT-CHARTER.md) first.** The maintainer's
primary goal is authenticated ciphertext **in public Git** combined with
transparent plaintext **in an unlocked local checkout**; local-at-rest and
same-UID privacy are optional rather than hard prerequisites. Arbitrary Git
attribute patterns, default persistent local unlock, normal Git rename and a
one-time legacy transition are now high-priority targets. The previous
security-hardening stopping criterion is superseded: continually reassess
security, correctness, usability, simplicity, portability and proofs.

**Current source `861975a` is not yet that UX:** the existing v3 uses
`*.secret`, a required memory-only agent and default private-permission
hardening. Keep describing those accurately until changed. The format uses
Argon2id + AES-SIV with exact canonical Git path binding. Maintain the
independent v3 byte specification and existing source-derived Lean proofs;
never change cipher semantics silently or import legacy CBC into the proved
core. Treat the [independent review triage](V3-REVIEW-TRIAGE.md), particularly
F-02/F-03, as actionable engineering inputs.

## Where things are

| Concern | Canonical location |
| --- | --- |
| Product vision, security promise, goals/non-goals | `docs/verification/V3-PRODUCT-CHARTER.md` |
| Independent review, scope classification and open reproductions | `docs/verification/V3-REVIEW-TRIAGE.md` |
| Roadmap, stage status, remaining work | `docs/verification/V3-ROADMAP.md` |
| Evidence per requirement | `docs/verification/V3-PROOF-COVERAGE.md` |
| Trust-ordered assumptions, adapter call-site table | `docs/verification/V3-ASSUMPTIONS.md` |
| Internal security review (V6) | `docs/verification/V3-SECURITY-REVIEW.md` |
| User documentation | `docs/verification/V3-USER-GUIDE.md` |
| Bash ↔ v3 command and mechanism map | `docs/verification/V3-BASH-CORRESPONDENCE.md` |
| Wire/AAD/Git behavior | `docs/verification/specs/V3-AUTHENTICATED-P0.md` |
| Verified pure core (codec + every decision) | `rust/crates/transcrypt-v3-core/src/lib.rs` |
| Crypto primitives (`Keyed: V3Primitives`), KDF | `rust/crates/transcrypt-v3/src/lib.rs` |
| Git adapter, agent, fd-relative FS | `rust/crates/transcrypt-v3/src/{main,git,worktree,setup,audit,session,fsat}.rs` (module map in `main.rs`) |
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

## Adapter invariants (current baseline; revise intentionally under the charter)

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
- **Current code:** smudge emits plaintext only when `umask_is_private()`;
  otherwise Git receives the record and hooks hydrate with mode 0600. This
  is an implementation detail of the **current strict privacy default**, not
  a requirement to retain it in the proposed ordinary-local-plaintext mode.
  Any replacement must preserve public-Git encryption correctness and make
  opt-in strict mode truthful.
- `hydrate` replaces only files that are authentic records for their path,
  and re-indexes only files holding the staged plaintext.
- Run every subprocess through `run_bounded` (directly or via `git`,
  `git_with_input`, `output`); never `Command::output()`.

## Product state (checkpoint)

**Commands.** `init`, `unlock`, `hydrate`, `status`, `doctor`,
`verify-index`, `audit`, `lock`, `rekey`, `uninstall`.

**Git integration.**
- Long-running `filter-process`, with per-file `clean`/`smudge` as the
  fallback.
- Merge and diff drivers.
- Hooks:
  - `pre-commit` (`verify-index`) and `pre-push` (`audit`) are required;
  - `post-checkout`, `post-merge` and `post-rewrite` (`hydrate --auto`) are
    optional.
- Server-side: `contrib/v3/pre-receive` and
  `contrib/v3/check-remote-enforcement`.

**Supported layouts.** Ordinary checkouts, linked worktrees (one shared
agent; `lock` flushes all of them) and submodules.

**Plaintext permissions.**
- Git never writes plaintext readable by others (umask-aware smudge).
- `hydrate` and the clean filter make plaintext private.

**Gates at this checkpoint (all passing).**
- 105 Rust tests.
- Python vectors, the differential corpus and the Git transport tests.
- Snapshot verify/compare.
- Tracked Lean build (1750 jobs); 36 headline theorems on standard axioms.
- Darwin type-check.

The branch is unpushed: push needs the owner's credentials.

## Next tasks (product-directed; resume after each checkpoint)

1. Read the [charter](V3-PRODUCT-CHARTER.md) and the
   [independent review triage](V3-REVIEW-TRIAGE.md). Reproduce/repair **F-02
   rekey symlink overwrite** and **F-03 git-mv path binding** with the compiled
   Rust CLI. These are correctness/security problems, not optional workstation
   privacy features. Check current HEAD first: the report was against `861975a`.
2. Make **arbitrary Git `.gitattributes`-selected paths** the true policy.
   Generalize the production Rust and its Aeneas-derived Lean proof to
   canonical Git paths without a hardcoded `.secret` suffix; verify staged
   selection, keyless audit limitations, historical paths, and renames.
3. Make **local persistent derived credential** the default. `.git/config`
   is acceptable, or a private local sidecar if it gives clearer/simpler
   semantics; never commit keys. No agent required in everyday use. Keep
   session-only memory agent and stricter local permission checks optional.
4. Make normal Git operations transparent under ordinary umasks. The user is
   responsible for local plaintext visibility; ensure there is no *public*
   plaintext publication through normally configured encryption filters.
5. Build a **recoverable one-time Bash v2 → Rust v3 transition** preserving
   arbitrary selected paths. Document historical exposure; no runtime legacy
   cipher decoder or Bash v3 requirement.
6. Preserve compiled Aeneas/Lean source-derived proofs, update actual
   adapter-to-core assumptions and rerun regression/differential/fault tests.
   Obtain outside crypto/adapter review before security-sensitive release.

Remote enforcement is an **optional organizational control** (A13), not a
hard dependency for using the product. Keyless enforcement detects obvious
plaintext/structure, not forged authentication (A14). Same-UID adversaries,
rollback, deterministic equality and unlocked-worktree visibility are stated
bounds rather than default hardening targets.

After each meaningful task, independently select the next improvement with
best real-world value. A green test suite or exhausted previous agent backlog
is a checkpoint, **not the final product stopping condition**. If an
execution session ends, leave the exact next action and any open test/proof
failures rather than declaring the product done.
