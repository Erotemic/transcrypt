# Transcrypt v3: durable handoff for the next contributor or agent

**Last reconciled:** 2026-10-26, after review round 9 (sorted listings,
binary-search lookups and object orders in the verified core; A24), on top
of the end-to-end campaign (the
pre-commit hook's inputs, the stored-key decision and object replies moved
into the verified core; the end-to-end statement
[V3-SECURITY-ARGUMENT](V3-SECURITY-ARGUMENT.md)), on top of the
product-charter campaign (attribute selection, stored-key unlock, renames,
migration, review F-01 to F-04). **Branch:** `work/m2-nul-safe-path-enumeration`. Always begin by
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
| End-to-end statement and its hypotheses | `docs/verification/V3-SECURITY-ARGUMENT.md`, `proofs/aeneas/v3/V3Wire/Verification/EndToEnd.lean` |
| Trust-ordered assumptions, adapter call-site table | `docs/verification/V3-ASSUMPTIONS.md` |
| Internal security review (V6) | `docs/verification/V3-SECURITY-REVIEW.md` |
| User documentation | `docs/verification/V3-USER-GUIDE.md` |
| Bash ↔ v3 command and mechanism map | `docs/verification/V3-BASH-CORRESPONDENCE.md` |
| Wire/AAD/Git behavior | `docs/verification/specs/V3-AUTHENTICATED-P0.md` |
| Verified pure core (codec + every decision) | `rust/crates/transcrypt-v3-core/src/lib.rs` |
| Crypto primitives (`Keyed: V3Primitives`), KDF | `rust/crates/transcrypt-v3/src/lib.rs` |
| Git adapter, credentials, fd-relative FS | `rust/crates/transcrypt-v3/src/*.rs`: filters, lifecycle, credentials, Git, worktree, setup, attributes, rekey, audit, migrate, agent, fd-relative FS (module map in `main.rs`) |
| Independent Lean spec | `proofs/lean/Transcrypt/{V3Wire,V3WireCodec,V3Policy}.lean` |
| Generated Lean (do not edit) | `proofs/aeneas/v3/V3Wire/Extraction/` |
| Proofs | `proofs/aeneas/v3/V3Wire/Verification/{Copy,Codec,Bytes,Path,Attr,Index,Envelope,Filters,Frame,Pkt,Protocol,Lifecycle,Snapshot,Objects,EndToEnd}.lean` |
| Theorem ledger | `proofs/aeneas/v3/PROOF-STATUS.md` |
| Tests | `rust/crates/transcrypt-v3/tests/{workflows,git_lifecycle,adversarial,v3_vectors,v3_differential}.rs`, `tests/v3/reference/` (`differential.py` regenerates the OpenSSL/argon2 corpus); Bash v2: `tests/v2`, `tests/v3` (bats) |

## Verified state

- Every function of the core is translated by the pinned cargo-hax 0.4.2
  (Charon + Aeneas) toolchain and proved against the independent spec,
  covering full outputs, every error outcome and the absence of panics.
  Protocol theorems are relative to the explicit primitive contract
  `Realizes`. Lifecycle theorems are about Lean models of the adapter's
  loops.
- The pre-commit hook's inputs are verified functions of Git's exact
  listings (`Snapshot.lean`: `parse_listing`, which also checks Git's byte
  order of paths with `bytes_lt`, each path once; `listing_fields`,
  `parse_listing_attrs`, `first_unselectable`, `held_entries` (binary
  search), `is_local_change`, `object_order_ok`, `next_move_source`,
  `blob_elsewhere` (through object orders)), as are the stored-key decision
  and `cat-file --batch` framing (`Objects.lean`). `EndToEnd.lean` states
  what an accepted commit guarantees, with every Git/crypto/adapter
  contract a named hypothesis (`hook_accepts_only_authenticated_ciphertext`,
  `hook_accepts_only_authenticated_ciphertext_given_history` with A24,
  `hook_repairs_only_local_changes`,
  `stored_key_authenticates_current_config`).
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
scripts/build-release.sh --test   # static Linux x86_64/arm64 archives in dist/ (docs/RELEASING.md)
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
- Reuse the proved helpers (`matches_at`, `find_byte`, `bytes_eq`) in the
  core instead of writing new loops: a call is one `step` with the helper's
  spec, a new loop is an invariant proof.
- A `bool` *value* built with `||` (e.g. `let ok = a || b;`) translates to
  Lean that does not typecheck; use `|` there (conditions are fine).
- After `step`/`simp`, a loop's `cont` post `inv ∧ measure` is often
  flattened to `A ∧ B ∧ … ∧ M` (with `if true` simplified): give flat
  anonymous constructors. When the invariant is a named definition, it is
  *not* unfolded: use `refine And.intro ?_ ?_` and `unfold` it.
- To prove a post containing `match r with …` from a lemma, do not
  `apply` a lemma whose post spells the `match` itself (the generated
  matchers differ and unification fails): prove a match-free post
  (equations `r = cont …`) and use `WP.spec_mono`.
- `spec_result` (in `EndToEnd.lean`): from `m ⦃P⦄` and `m = ok r` obtain
  `P r`, so theorems can take the adapter's observed results as
  hypotheses.
- `simp` folds `l[i] :: l.drop (i+1)` back into `l.drop i`
  (`List.getElem_cons_drop`); use `simp only` after such a rewrite.
- Inside `first`/`try`, multi-line parenthesized tactic blocks must align;
  use one-line `;` chains or `case` instead. `cases h : b` does not rewrite
  hypotheses mentioning `b`; rewrite them with `h`.
- Prop-valued structures cannot have data fields (use `∃`). `to` is a
  keyword (name binders `to_`).
- A new core function whose name equals a parameter name elsewhere renames
  that parameter in the generated code (`local_change1`): pick distinct
  names (`is_local_change`).
- Listings are sorted (the parse proves it), so lookups are binary
  searches: `find_path`/`find_object` keep `low ≤ high` with "everything
  before `low` is before the target, nothing from `high` on is" and use
  `loop.spec_decr_nat` with measure `high - low`; monotonicity comes from
  `List.pairwise_iff_getElem` on `Sorted`/`PathOrdered`/`ObjectOrder`.
  Lookups by object id take an *object order* the adapter sorts and the
  core checks (`object_order_ok`); that each record has a slot is
  pigeonhole (`ObjectOrder.surj`, via `Finset.eq_of_subset_of_card_le`).
- Aeneas refuses an early `return` from a loop nested inside a `match`
  arm ("Early returns inside of loops are not supported"): put the loop in
  its own function (`move_source_from`).
- `!f(x)` as a bool *value* (not a condition) translates to a `Prop` and
  fails to typecheck, like `||`; write the value positively
  (`bytes_lt(a, b) | bytes_eq(a, b)` for "not after").
- The posts of `loop.spec_decr_nat` bodies are flattened: give
  `⟨inv₁, …, invₙ, measure⟩`, not nested pairs. State invariants with
  `order.val.length` rather than `order.length` so `xs[i]` index proofs
  are found automatically.
- After `simp only [Slice.len …]`, a trailing `let n ← len xs; ok (done n)`
  becomes `ok (done xs.len)`; finish with `simp only [WP.spec_ok]`, not
  `step`. Dot notation on a `def` over `List.Pairwise` (e.g.
  `hO.lt_of_le` for `PathOrdered`) fails; call `PathOrdered.lt_of_le hO`.

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
  (Git's attributes, parsed by `parse_attr_record`), or, for an index
  snapshot, `listing_flags` (checked against the listing's own paths);
  never match patterns in Rust.
- Hold index and tree snapshots as `Listing`s (the verified
  `parse_listing`, each path once; entries from `listing_fields`), and
  compute the hook's inputs (membership in `HEAD`/`HEAD^1`/incoming, local
  changes, move sources, the keyless move check) only with the verified
  functions over them; `EndToEnd.lean`'s `HookRun` lists the calls the hook
  relies on. Object orders come only from `Listing::object_order` (checked
  by `object_order_ok`); several trees are combined only by
  `Listing::merge` (the one `unique = false` parse).
- Count a protected entry as settled (skipping authentication) only if
  `HEAD` and `HEAD^1` hold it and no attribute file and not the config
  changed since them (A24, H-77).
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
  `git_with_input`, `output`, `run_bounded_status`); never
  `Command::output()` or `.status()`. Write to a pipe or socket only inside
  `sigpipe_blocked` (`run_bounded` does): `main` gives SIGPIPE its default
  action, so an unguarded write to a subprocess that exited early kills
  the process silently, skipping rollback.
- Read untrusted input with `read_record` (bounded, wiped as it grows).
- The one `git add` with repository-derived paths is `migrate`'s
  `--renormalize` (which `update-index` lacks); it is safe only because
  every Git command runs with `GIT_LITERAL_PATHSPECS`.

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
- Rust: 152 tests across the workspace.
- Bash: 218 bats tests.
- Python vectors, the differential corpus and the Git transport tests.
- Snapshot verify/compare.
- Tracked Lean build; axiom audit (see PROOF-STATUS).

The branch is unpushed: push needs the owner's credentials.

## Next tasks (resume after each checkpoint)

1. **Adversarial agent review: converged.** Seven rounds (H-28 to H-73 in
   [V3-SECURITY-REVIEW](V3-SECURITY-REVIEW.md)) ended with nothing above
   Low. The invariants that got there are the design rules for new code:
   - interruption fails closed, and rerunning converges;
   - the hooks accept what the audit accepts (or are stricter);
   - the `transcrypt` macro must resolve to the filter, checked on real
     paths too;
   - attribute queries are case-sensitive;
   - records of other configs pass only as Git's own blobs;
   - Git's listings are trusted only after the verified parse checked their
     order (each path once), and verified lookups stay sublinear (H-75,
     H-76); an entry skips authentication only while the selection is
     unchanged (H-77, A24).

   Round 9 (H-75 to H-77) reviewed the verified snapshot functions. Run a
   fresh round on any substantial change. The external human review
   (R-01) is deliberately the **final** step; it is not a blocker for
   ongoing work.
2. **Done:** the rebind decision is the verified `seal_action`
   (`sealSpec_repairs_only_local`), and its inputs are verified functions
   of Git's listings (`hook_repairs_only_local_changes`). Remaining on the
   hook path (A4 residual, see the assumption register): a verified
   `ls-tree` record parser instead of the `tree_record` rewrite, and the
   unprotected-entry checks on `held_entries`.
3. **Renames across branches** conflict as modify/delete, because Git's
   content-based rename detection cannot match path-bound ciphertext
   (tested, documented). A rename-aware merge driver cannot help, since Git
   never calls it. A future option is a `status`/`hydrate` hint that pairs
   the deleted and added files by decrypted content.
4. **Done:** selection parsing is the verified `parse_attr_response` (and,
   for the index, `parse_listing_attrs`); the stored-key load is
   `stored_key_state` (`stored_key_authenticates_current_config`); object
   replies are `parse_batch_header`/`blob_read`. Next A4 narrowings: the
   inputs of smudge/hydrate/lock (worktree reads), the filter-process
   key/value lines, and the audit's per-commit loop (an end-to-end
   statement for `audit` like the hook's).
5. **Done:** the private-mode agent's optional idle timeout (`--timeout`).
6. **Performance** (release build, 10 000 files, 300 protected): a commit
   with the hook takes 0.24 s, a protected edit 0.27 s, a `git mv` of a
   protected file 0.36 s, `git status` 0.04 s. The hook reads the
   index once, and authenticates only entries that differ from `HEAD` or
   `HEAD^1` (the others get the keyless checks; H-74, A24). Every snapshot
   lookup is a binary search (H-75): `verify-index` after rewriting 60 000
   unprotected files takes 5.3 s (it was 32 s with linear scans), a locked
   `verify-index` of a merge bringing 10 000 protected files 0.35 s.
   Every blob the adapter stages (hook sealing and re-binding, `rekey`,
   `reencrypt`, `unprotect`) goes through `git::IndexUpdate`: one `git
   fast-import --done` reading the contents from stdin (no temporary
   files) and one `update-index`. A commit renaming 2 000 protected files
   takes 0.54 s (it was 10.9 s with one `hash-object` process per file,
   which also triggered an automatic `git gc`).
7. **Simplification passes (two, reviewer-driven) are done**: shared
   helpers in `git.rs` (one check-attr builder, one listing parser,
   `push_blob_record`, `read_record`, `sigpipe_blocked`), one index
   snapshot per hook run, `filter.rs`/`attributes.rs`/`rekey.rs` split out
   of `main.rs`/`setup.rs`, shared test helpers in `tests/common`. Review
   round 8 checked the refactor (no regression; H-74 found and fixed). The
   legacy crates (`transcrypt-policy`, `transcrypt-legacy*`,
   `transcrypt-protocol`), unused by v3, now live in their own workspace,
   `rust-legacy/` (owner decision), still tested in CI as the v2 parity
   evidence against Bash and as the source of the historical SMT and
   source-model checks (`proofs/smt`, `proofs/sourcecheck`).

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
