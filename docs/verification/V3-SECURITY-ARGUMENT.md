# Transcrypt v3: the end-to-end security argument

**Written 2026-10-26; settled entries and A24 added the same day (review
round 9); the product theorems and the A24 induction added 2026-11-01
(`ProductSecurity.lean`).** This document states, in one place, what the
machine-checked proofs say about the product's main promise and exactly
which assumptions that statement rests on. It is the readable companion of
[`EndToEnd.lean`](../../proofs/aeneas/v3/V3Wire/Verification/EndToEnd.lean).
Assumption IDs refer to the [assumption register](V3-ASSUMPTIONS.md);
evidence levels follow the [proof ledger](V3-PROOF-COVERAGE.md) (PROVED is
never used for TESTED or REVIEWED evidence). For a short summary, one card per product
guarantee, start with [V3-PRODUCT-GUARANTEES](V3-PRODUCT-GUARANTEES.md).

## The promise

From the [product charter](V3-PRODUCT-CHARTER.md): *user-selected files are
authenticated ciphertext in public Git history.* Selection is Git's own
attribute evaluation (`filter=transcrypt-v3`, usually through the
`transcrypt` macro).

The last code that sees a commit before Git records it is the `pre-commit`
hook. The argument therefore has three parts:

1. **What the hook accepts.** If the hook accepts, every path the committed
   attributes select is stored as a record that authenticates at that path
   under the committed configuration (Theorem 1).
2. **What the hook changes.** Before checking, the hook re-encrypts some
   entries. It only ever re-encrypts the user's own local changes, so a
   hostile commit cannot be laundered into genuine records (Theorem 2).
3. **Which key.** The key the hook uses is the stored key only if it was
   stored for, and authenticates, exactly the current configuration
   (Theorem 3).

## Theorem 1: the hook accepts only authenticated ciphertext

`hook_accepts_only_authenticated_ciphertext`, in prose:

> Let `g` be what Git holds when the hook runs: the index it will commit,
> `HEAD`, `HEAD^1`, each path's effective `filter` value under the
> attributes being committed, and the object store. Assume:
>
> * Git printed the index, `HEAD` and `HEAD^1` listings exactly (**A20**;
>   that they are sorted is not assumed: the verified parse checks it);
> * Git's `check-attr --cached` answer gives each index path's effective
>   `filter` value under the committed attributes (**A19**);
> * each blob the hook checked is the content of its entry's object id
>   (**A11**, **A21**);
> * the cryptographic primitives realize the abstract AES-SIV suite `σ`,
>   whose truncated SHA-256 is the configuration id (**A5**);
> * the configuration used is the one staged as `.transcrypt/config`
>   (checked by the adapter, **A4**);
> * the adapter acted only on the verified core's results, as listed in
>   `HookEvidence`, and its per-entry check is at least as strict as the model
>   `hookEntry` (**A4**).
>
> If the hook accepted, then the index, `HEAD` and `HEAD^1` list each path
> once, in Git's byte order (`Sorted`), and every entry of the index whose
> path the committed attributes select is a **regular file** (not a symlink
> or submodule), **not reserved metadata**, and its blob:
>
> * **unlocked:** authenticates at exactly that path under the committed
>   configuration (`OpensTo σ config path blob pt`); in the incremental
>   pre-commit hook an entry unchanged since both `HEAD` and `HEAD^1`
>   (*settled*) may instead carry the v3 envelope of that configuration;
> * **locked:** has the v3 envelope of that configuration, and is either
>   unchanged since `HEAD` and `HEAD^1` or is not the blob of another path
>   (no record moved without the key).
>
> Git then commits that index (**A22**).

Formally the conclusion is `ConfigCommitted g config ∧ SnapshotsSorted g ∧
AcceptedIndex σ config keyed incremental g`, where `AcceptedIndex` says each
selected entry is an `AcceptedProtectedEntry`: `Selectable`, with a blob that
satisfies `KeyedEntryOk` (unlocked) or `KeylessEnvelopeOk` (locked). These
are named definitions in `EndToEnd.lean`, next to the intermediate lemmas
(`hook_snapshots_sorted`, `hook_flags`, `hook_selectable`,
`hook_checks_selected`, `EntryAccepted.accepted`) the proof is built from.

Together with AES-SIV unforgeability (**A10**), "authenticates at that path
under the committed configuration" means the blob is ciphertext produced
with the repository key for that path; `opensTo_unique` makes the plaintext
unique.

### Settled entries and the checked history (A24)

The incremental hook trusts history for settled entries, so that an
ordinary commit does not decrypt every protected file (0.24 s for 10 000
files). What it trusts is a named assumption:

> **A24.** Every entry of `HEAD` whose path the committed attributes select
> authenticates at its path under the committed configuration
> (`HeadAuthentic`).

`hook_accepts_only_authenticated_ciphertext_given_history` proves that
with A24, a commit the hook accepted with the key stores at **every**
selected path a record that authenticates there, settled or not.

The induction that discharges A24 is now proved
(`ProductSecurity.lean`, PROVED (model)), in three steps:

1. **Bootstrap** (`hook_full_check_authenticates`). A keyed check that
   authenticated every protected entry (`FullCheck`: not incremental, or
   no entry counted as settled) gives `AuthenticatedIndex` with no
   hypothesis about history. `pre_commit_check_modes` states the three
   modes side by side: full keyed (authenticated, no history), incremental
   keyed (`AcceptedIndex`; authenticated given `HeadAuthentic`), keyless
   (the envelope only, A14).
2. **One transition** (`head_authentic_of_checked_commit`). If the checked
   index authenticates under `config`, the next commit's `HEAD` was made
   from it (`CommitStep`: every entry of the next `HEAD` is a checked index
   entry, A22; objects keep their content, A11), and the policy is
   unchanged (`PolicyUnchanged`: no path newly selected, the same committed
   configuration), then the next `HEAD` is authentic (`HeadAuthentic`).
3. **Induction** (`keyed_history_stays_authenticated`). In a history of
   keyed commits under one key, each made from the index checked before it,
   checked incrementally only when the policy is unchanged (otherwise in
   full), and starting with a full check (or an authentic `HEAD`), every
   commit's selected entries authenticate.

`HEAD` and `HEAD^1` are sorted (each path once; checked by the verified
parse, review H-76), so the entry that holds a settled blob is *the* entry
at that path (`Sorted.holds_oid`): a crafted tree that lists a path twice
is refused instead of letting one checked entry stand for another.

What remains assumed:

* **`CommitStep`**: Git commits the index the hook checked (A22), and an
  object id names one content (A11).
* **`PolicyUnchanged`** before an incremental check: the adapter counts an
  entry as settled only while no attribute file and not the configuration
  changed since `HEAD` and `HEAD^1` (review H-77); otherwise nothing is
  settled, which is a `FullCheck`. That the guard gives `PolicyUnchanged`
  rests on A19 and on the guard's own refinement, which is separate work
  and plugs in as this hypothesis.
* **The start of history.** Commits made without the keyed hook
  (`--no-verify`, cherry-pick and rebase, a locked checkout, pulled
  commits, other parties) are outside the induction. For them A24 rests
  on the keyed `audit` (pre-push, A13), which authenticates every changed
  entry and, when the attributes or the configuration change, the whole
  tree, or on a full check (`verify-index` authenticates everything).

### How the proof goes

Every step is a theorem about the Aeneas translation of the production
`transcrypt-v3-core`, stated against the independent specification
`V3Policy.lean`:

| Step | Verified function (theorem) | Spec |
| --- | --- | --- |
| The index listing is exactly Git's entries, record ends recorded | `parse_listing` (`parse_listing_spec`, both directions) | `listingBytes`, `EntryOk` |
| Each entry's mode, object id and path | `listing_fields` (`listing_fields_spec`, `FieldsOf.slices`) | `Entry` |
| The protected flags are Git's selection of exactly those paths | `parse_listing_attrs` (`parse_listing_attrs_spec`, both directions) | `attrResponse`, `Selected` |
| No protected entry is a symlink, submodule or metadata | `first_unselectable` (`first_unselectable_spec`) | `Selectable` |
| The listings are in Git's order, each path once | `parse_listing` with `bytes_lt`, `listing_ordered` (`parse_listing_spec`, `bytes_lt_spec`) | `BytesLt`, `Sorted` |
| Unchanged since `HEAD` and `HEAD^1` | `held_entries` (`held_entries_spec`; binary search, `find_entry_spec`) | `Holds`, `Settled` |
| The keyless move check | `blob_elsewhere` (`blob_elsewhere_spec`), through object orders checked by `object_order_ok` (`object_order_ok_spec`) | `BlobElsewhere` |
| How each protected entry is checked (authenticated, or the envelope with or without the move check) | `entry_check` (`entry_check_spec`), which `check_staged` and `hookEntry` both dispatch on | the cases of `EntryAccepted` |
| Each protected blob authenticates at its path | `open_record` (`open_record_spec`), in the model `hookPlan` (`hookPlan_spec`) | `OpensTo` |
| Without the key: the envelope | `record_envelope_ok` (`record_envelope_ok_spec`) | `EnvelopeOk` |
| Object replies are for the requested id and announced size | `parse_batch_header`, `blob_read` (`parse_batch_header_spec`, `blob_read_spec`) | `BatchHeader`, `blobReadSpec` |

`hookPlan` is a small Lean model of the loop in
`transcrypt_rs::lifecycle::check_staged` (like the existing `verifyPlan`);
it calls the generated functions, and takes which check each entry gets from
the generated `entry_check`, as the Rust loop does. That the Rust loop
matches it is part of A4 (reviewed, tested).

## Theorem 2: the hook repairs only local changes

`hook_repairs_only_local_changes`, in prose:

> For a protected index entry, suppose the hook asked the verified core
> where its content came from (`entry_provenance`: a `Provenance`, from
> `HEAD` and the commits being merged, picked, reverted or rebased, which
> are consulted only when some protected entry changed), read the blob and
> found what it is (a `RecordClass`: it opens at its own path
> (`open_record`); it has no v3 header (`parse_file_header`); it opens at
> the path of `HEAD` record `j`, a move source from `next_move_source`; or
> none of these), and the verified `repair_plan` decided on the two. Assume
> Git's listings are exact (**A20**) and the sequencing state names the
> commits being brought in (**A23**). If `repair_plan` decided to seal or
> re-seal the entry, then:
>
> * its provenance is exactly where its content came from (`ProvenanceIs`),
>   and it is **the user's change** (`UserStaged`: neither `HEAD` nor any
>   incoming commit holds that blob at that path, and the incoming commits
>   are known), unless `protect` forced it and it is sealed; so it is a
>   `LocalChange`;
> * it did not already authenticate at its path;
> * only plaintext (no v3 header) is sealed;
> * a rebind from `HEAD` record `j` re-encrypts exactly the plaintext of a
>   record that authenticates at the path of that record (`MoveSource`:
>   same blob, another path, whose own entry has left the index).

`hook_skips_only_unrepairable`: an entry whose blob the hook does not read
(the verified `needs_record` says it cannot be repaired) is neither the
user's change nor forced, so skipping it misses no repair.

So content that arrives in a commit is only ever checked by Theorem 1,
never repaired: a hostile commit that moves a record or adds plaintext is
refused, not laundered (`repairSpec_repairs_only_local`, with the
provenance and the decision proved about the generated code).

## Theorem 3: the key is the one for this configuration

`stored_key_authenticates_current_config`: `Key::load` uses a stored key
only when the verified `stored_key_state` says `Unlocked`. Then the key
file holds exactly the current configuration followed by the key, and the
key authenticates that configuration (`ConfigAuthentic`, relative to
**A5**). The adapter builds the primitives from the file's key bytes
(**A17**).

## The product theorems (`ProductSecurity.lean`)

The theorems above are restated, and composed, as a short portfolio over
named predicates; each keeps its external hypotheses visible.

| Guarantee | Theorem | What it composes |
| --- | --- | --- |
| A. Authenticated publication | `keyed_publication_authenticates`: `HookContracts`, `Realizes`, `ConfigCommitted` and an accepted keyed check (`KeyedCheckAccepted` in a `CheckMode`) give `AuthenticatedIndex`; `HeadAuthentic` is needed only for an incremental check | `hook_full_check_authenticates` (new), `hook_accepts_only_authenticated_ciphertext_given_history` |
| Check modes | `pre_commit_check_modes` | Theorem 1 in each mode |
| A24 history | `head_authentic_of_checked_commit`, `keyed_history_stays_authenticated` | the above, by induction (new) |
| B. Authenticated recovery | `checkout_releases_only_authenticated_plaintext`: smudge's output either differs from the stored record and is exactly the plaintext it authenticates to at that path and configuration, or is the record itself, unchanged, with the v3 envelope (locked, another configuration, private mode); a record it decided to open that does not authenticate is refused. `checkout_opens_genuine_records`: a genuine record of this configuration opens to its plaintext | `smudgeModel_spec`, `smudge_action_spec`, `open_record_complete`, `opensTo_envelopeOk`, `sealed_length` |
| C. No laundering | `repair_never_launders`: seals only the user's change or forced plaintext (no v3 header); rebinds only the user's record that authenticates at its move source; content imported from `HEAD` or an incoming commit is never rebound, and sealed only when `protect` forced it; the user's change is never skipped | `hook_repairs_only_local_changes`, `hook_skips_only_unrepairable`, `repair_plan_repairs_only_local`, `UserStaged.not_committed` |
| D. Configuration-bound key | `stored_key_binds_file_operations`: when the stored key is used, its file holds the current configuration, the key authenticates it, and every record it opens or seals is bound to that configuration and path | `stored_key_authenticates_current_config`, `open_record_spec`, `seal_record_spec`, `seal_opens` |

Not claimed: that every successful smudge yields plaintext (a kept record
is a success), Argon2id security or where a key came from (A10, A17), or
anything about commits outside a keyed history (A13).

## Hypotheses and where they are discharged

| Hypothesis in Lean | Meaning | Assumption | Evidence |
| --- | --- | --- | --- |
| `GitListing run.index.bytes g.index` (and `HEAD`, `HEAD^1`, incoming; `HookContracts`) | Git's listing is exactly its snapshot | A20 (refines A7) | TESTED (real Git, all lifecycle suites); the parse and the path order PROVED |
| `GitAttributes g run.response` | `check-attr --cached` reports the committed attributes | A19 | TESTED (Git 2.43, CI 2.34); the parse PROVED |
| `GitObject g oid record` | bytes read by id are that object | A11, A21 | header and size decision PROVED; reading exactly the size and the LF TESTED; object identity ASSUMED (Git's hash) |
| `Realizes inst prims σ` | the primitives compute AES-SIV / SHA-256 | A5 (with A9) | TESTED (vectors, differential) |
| `hid : wireBytes id = σ.digest16 config` | the configuration id is the suite's digest | A5 | TESTED (vectors) |
| `hcfg : ConfigCommitted g config` | the configuration used is the staged `.transcrypt/config` | A4 | REVIEWED + TESTED (`check_staged` compares the staged blob with it) |
| `run : HookEvidence g`, `hookPlan … = ok true`; `RepairContracts` (Theorem 2: `provenance`, `decision`, and `record`, what each reported `RecordClass` means, `RecordEvidence`) | the adapter called the verified functions on these inputs, reports its evidence about each blob truthfully and acted on their results | A4 | REVIEWED + TESTED; the functions PROVED |
| Git commits `g.index` | the commit is the index the hook checked last | A22 (refines A7) | TESTED (every pre-commit test) |
| `RepairContracts.incoming`, `.lazy` (Theorem 2) | the incoming commits are those named by the sequencing state | A23 | TESTED (merge, octopus, cherry-pick, rebase suites) |
| `HeadAuthentic` (corollary; only for an incremental check) | the history the incremental hook trusts was checked | A24 | induction PROVED (model) (`keyed_history_stays_authenticated`); its start REVIEWED + TESTED (audit, A13; `newly_protected_files_are_authenticated_by_the_hook`, `trees_listing_a_path_twice_are_refused`) |
| `CommitStep` (history) | the next `HEAD` is the checked index; objects keep their content | A22, A11 | TESTED; ASSUMED |
| `PolicyUnchanged` (history, before an incremental check) | no path newly selected; same committed configuration | A19 + the hook's policy guard | TESTED + REVIEWED; the guard's refinement is separate work |
| Unforgeability | only the key holder makes records that authenticate | A10 | ASSUMED (standard) |

## What is proved, tested and trusted

* **PROVED (source-derived):** every decision listed in the tables above;
  all are theorems about the generated translation of the production core
  (the 132 theorems of the ledger `proofs/aeneas/v3/PROOF-STATUS.md`,
  standard axioms only:
  `bash proofs/aeneas/check-v3-axioms.sh`).
* **PROVED (model):** the composition `hookPlan_spec` and the end-to-end
  theorems (with the A24 corollary), the product theorems and the A24
  induction (`ProductSecurity.lean`), about Lean models that call the
  generated functions.
* **TESTED:** that the Rust adapter matches the models and contracts
  (A4), Git's behavior (A7, A19–A23), the primitives (A5, A9); the
  discharge of A24 by the hook and the audit (also REVIEWED).
* **TRUSTED:** Lean and the Charon/Aeneas translation (A3), Git's object
  identity (A11), cryptographic hardness (A10).

## What the statement does not cover

* **Commits made without the hook** (`--no-verify`, a clone that never ran
  `unlock`, merges that skip `pre-commit`): the `pre-push` hook and
  `audit` check history (A13); `audit` is not part of this statement.
* **Keyless forgery:** without the key, only the envelope is checked
  (A14); the next unlocked check or keyed audit authenticates.
* **Unprotected files:** the hook's extra refusals for unprotected entries
  (a record moved to an unprotected name, a file that lost its protection)
  are adapter code, tested to match `audit`; they are not needed for the
  promise about selected paths.
* **Local privacy:** smudge, hydrate, lock and the private mode have their
  own lifecycle theorems (`smudgeModel_spec`, `hydratePlan_spec`,
  `lockEntry_spec`); workstation privacy is an optional mode (charter).

## Re-checking

```bash
bash proofs/aeneas/build-v3-tracked.sh
bash proofs/aeneas/check-v3-axioms.sh
cd rust && cargo test --workspace
```
