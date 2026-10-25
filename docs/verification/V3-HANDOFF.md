# Transcrypt v3: durable handoff for the next contributor or agent

**Last reconciled:** 2026-10-25, after the product-charter campaign
(attribute selection, stored-key unlock, renames, migration, review F-01
to F-04). **Branch:** `work/m2-nul-safe-path-enumeration`. Always begin by
checking the working tree and latest commits; this file is a continuity
aid, not a claim about later changes.

## Product direction and current implementation

**Read [V3-PRODUCT-CHARTER](V3-PRODUCT-CHARTER.md) first.** The goal is
authenticated ciphertext **in public Git** with transparent plaintext **in
an unlocked local checkout**. Local-at-rest and same-UID privacy are an
optional mode, not prerequisites.

The implementation now follows it:
- **Selection by `.gitattributes`.** `protect PATTERN` writes
  `PATTERN transcrypt` (a committed macro for
  `filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text`).
  Git's `check-attr` answers are parsed by the verified core. The path
  policy is suffix-free, except for the reserved `.transcrypt/`,
  `.gitattributes` and `.gitmodules`.
- **Stored-key unlock.** `unlock` stores the derived key in
  `$GIT_COMMON_DIR/transcrypt-v3/key` (0600, not in `git config`). Every
  use authenticates the current config with it, so a pulled rekey makes it
  stale. `unlock --private` is the old memory-only agent plus 0600
  plaintext.
- **Renames.** The pre-commit hook re-encrypts local `git mv`s (and seals
  plaintext staged around the filter). It never re-encrypts content that
  came from a commit (no laundering), and keyless checks refuse moved
  records.
- **Migration.** `migrate` converts a Bash v2 checkout.
- **Safe writes.** Every v3 write to a repository file goes through
  `write_repository_file` (the F-02 fix).

The wire format is unchanged (profile 1). Maintain the independent v3 byte
specification and the source-derived Lean proofs. Never change cipher
semantics silently or import legacy CBC into the proved core.

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
| Git adapter, credentials, fd-relative FS | `rust/crates/transcrypt-v3/src/{main,lifecycle,credential,git,worktree,setup,audit,migrate,session,fsat}.rs` (module map in `main.rs`) |
| Independent Lean spec | `proofs/lean/Transcrypt/{V3Wire,V3WireCodec,V3Policy}.lean` |
| Generated Lean (do not edit) | `proofs/aeneas/v3/V3Wire/Extraction/` |
| Proofs | `proofs/aeneas/v3/V3Wire/Verification/{Copy,Codec,Bytes,Path,Attr,Index,Envelope,Filters,Frame,Pkt,Protocol,Lifecycle}.lean` |
| Theorem ledger | `proofs/aeneas/v3/PROOF-STATUS.md` |
| Tests | `rust/crates/transcrypt-v3/tests/{workflows,git_lifecycle,adversarial,v3_vectors,v3_differential}.rs`, `tests/v3/reference/` (`differential.py` regenerates the OpenSSL/argon2 corpus); Bash v2: `tests/v2`, `tests/v3` (bats) |

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

## Adapter invariants

Each has a regression test in `tests/adversarial.rs`, `tests/workflows.rs`
or `tests/git_lifecycle.rs`.

- Read Git objects only by object id, from one parsed snapshot, through
  `git_blob` (one shared `cat-file --batch` with exact reply framing,
  bounded). Never use `:<path>` revision syntax.
- Create Git subprocesses only with `git_command` (literal pathspecs, no
  replace refs). Never `git add -- <path>` with repository-derived paths;
  re-index with `update-index -z --stdin`.
- Decide what is protected only with `protected_flags` / `protected_entries`
  (Git's attributes, parsed by `parse_attr_record`); never match patterns
  in Rust.
- Replace a worktree file only through `Protected::replace` with the stamp
  from the read that justified it, while holding `staging_dir`. Write any
  other repository file only through `write_repository_file`.
- Get the key only through `credential::Key` (stored key authenticated
  against the current config, or the private agent). Release plaintext
  only through `open_record`. Without a key, clean passes through only
  inputs accepted by `record_envelope_ok`; smudge follows `smudge_action`.
- The pre-commit hook re-encrypts only local changes (`seal_staged`: staged
  blob ≠ `HEAD`'s, no merge/rebase in progress, rename source gone from the
  index). Never extend it to content from commits.
- `hydrate` replaces only files that are authentic records for their path,
  and re-indexes only files holding the staged plaintext.
- Run every subprocess through `run_bounded` (directly or via `git`,
  `git_with_input`, `output`); never `Command::output()`.

## Product state (checkpoint)

**Commands.** `init [PATTERN…]`, `protect`, `unprotect`, `unlock
[--private]`, `status`, `doctor`, `lock`, `rekey`, `hydrate`,
`verify-index`, `audit`, `migrate`, `uninstall`.

**Git integration.**
- Long-running `filter-process`, with per-file `clean`/`smudge` as the
  fallback.
- Merge and diff drivers, selected by the committed macro.
- Hooks:
  - `pre-commit` (seal and verify) and `pre-push` (`audit`) are required;
  - `pre-merge-commit` runs the read-only `verify-index` on merge commits;
  - `post-checkout`, `post-merge` and `post-rewrite` (`hydrate --auto`) only
    act in private mode.
- Server-side: `contrib/v3/pre-receive` and
  `contrib/v3/check-remote-enforcement` (canary with its own nested
  attributes).

**Supported layouts.** Ordinary checkouts, linked worktrees (one shared key;
`lock` flushes all of them), submodules, bare repositories (audit).

**Gates at this checkpoint.**
- Rust: 131 tests across the workspace.
- Bash: 218 bats tests.
- Python vectors, the differential corpus and the Git transport tests.
- Snapshot verify/compare.
- Tracked Lean build; axiom audit (see PROOF-STATUS).

The branch is unpushed: push needs the owner's credentials.

## Next tasks (resume after each checkpoint)

1. **Keep the adversarial agent review rounds going** on each new change
   (rounds so far: H-28 to H-51 in
   [V3-SECURITY-REVIEW](V3-SECURITY-REVIEW.md)). The external human review
   (R-01) is deliberately the **final** step, after engineering and proofs
   are pushed as far as they go; it is not a blocker for ongoing work.
2. **Done:** the rebind decision is the verified `seal_action`
   (`sealSpec_repairs_only_local`). Remaining: show the adapter computes its
   inputs (`local`, `moved`) correctly.
3. **Renames across branches** conflict as modify/delete, because Git's
   content-based rename detection cannot match path-bound ciphertext
   (tested, documented). A rename-aware merge driver cannot help, since Git
   never calls it. A future option is a `status`/`hydrate` hint that pairs
   the deleted and added files by decrypted content.
4. **Done:** selection parsing is the verified `parse_attr_response`. Next
   A4 narrowings: the inputs of `seal_action` and the stored-key load
   (authenticate before use).
5. **Done:** the private-mode agent's optional idle timeout (`--timeout`).

Remote enforcement is an **optional organizational control** (A13), not a
hard dependency for using the product. Keyless enforcement detects obvious
plaintext/structure and unbound moves, not forged authentication (A14).
Same-UID adversaries, rollback, deterministic equality and unlocked-worktree
visibility are stated bounds rather than default hardening targets.

After each meaningful task, independently select the next improvement with
best real-world value. A green test suite or exhausted previous agent backlog
is a checkpoint, **not the final product stopping condition**. If an
execution session ends, leave the exact next action and any open test/proof
failures rather than declaring the product done.
