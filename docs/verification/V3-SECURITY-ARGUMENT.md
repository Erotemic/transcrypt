# Transcrypt v3: the end-to-end security argument

**Written 2026-10-26; settled entries and A24 added the same day (review
round 9); the product theorems and the A24 induction added 2026-11-01
(`ProductSecurity.lean`); the keyed audit of one commit and the start of a
keyed history added 2026-11-02 (`Audit.lean`).** This document states, in one place, what the
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
>   `HookEvidence`: it checked every index entry with the verified
>   `staged_check` and `staged_verdict`, and answered the verdict's three
>   questions truthfully about the entry's own blob and path (`HookAnswers`:
>   whether it is a record of this configuration, whether it opens there
>   under `open_record`, whether it is another path's blob) (**A4**).
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
`hook_checks_every_entry`, `hook_entry_checked`) the proof is built from.

Together with AES-SIV unforgeability (**A10**), "authenticates at that path
under the committed configuration" means the blob is ciphertext produced
with the repository key for that path; `opensTo_unique` makes the plaintext
unique.

### Settled entries and the checked history (A24)

The incremental hook trusts history for what `HEAD` holds exactly, while
the committed attribute files and configuration are those of `HEAD` and
`HEAD^1` (the guard), so that an ordinary commit does not decrypt every
protected file (0.24 s for 10 000 files) or read any unchanged unprotected
file. What it trusts is a named assumption that does not mention
selection:

> **A24.** Every regular, non-reserved entry of `HEAD` whose blob has the
> committed configuration's envelope authenticates at its own path under
> that configuration (`RecordsAuthentic`).

Selection is deliberately absent: Git's selection also depends on local
attribute sources (`.git/info/attributes`, `core.attributesFile`, the
system file) that are not committed, so an invariant about `HEAD`'s
*selected* entries would not survive a local override that selects a path
holding a forged record while every committed attribute file stays the
same. (That earlier form, `HeadAuthentic`, remains a sufficient hypothesis
of the single-run `hook_accepts_only_authenticated_ciphertext_given_history`.)

The induction that discharges A24 is proved (`EndToEnd.lean`,
`ProductSecurity.lean`, PROVED (model) over the extracted `staged_check`,
`staged_verdict` and `held_records`):

1. **One run** (`hook_records_authentic`, `keyed_check_records_authentic`).
   A keyed check that accepted makes the index's records authenticate,
   given `HEAD`'s only when it trusted `HEAD` (incremental, guard `true`):
   an entry staged since `HEAD` was authenticated or is no record of this
   configuration (`NotRecord`); an unprotected file `HEAD` holds was
   authenticated if it is a record when `HEAD` was not trusted
   (`AuthenticateIfRecord`); and an entry was trusted only when `HEAD` holds
   its exact record, mode included (`held_records`). Every selected entry
   has the envelope, so it then authenticates
   (`hook_authenticated_of_records`).
2. **Bootstrap** (`hook_full_check_authenticates`). A keyed check that
   trusted nothing (`FullCheck`: not incremental, or the guard `false`)
   gives the invariant and `AuthenticatedIndex` with no hypothesis about
   history. `pre_commit_check_modes` states the three modes side by side.
3. **One transition** (`records_authentic_of_checked_commit`,
   `config_unchanged_of_guard`). The checked index's records are the next
   `HEAD`'s (`CommitStep`: every entry of the next `HEAD` is a checked
   index entry, A22; objects keep their content, A11), and a `true` guard
   of the next run keeps the configuration.
4. **Induction** (`keyed_history_authenticated_by_guard`). In a history of
   keyed commits under one key, each made from the index checked before it
   (`GuardedHistoryStep`), whatever each check's mode, every commit's
   records and selected entries authenticate, given only the start.

`HEAD` and `HEAD^1` are sorted (each path once; checked by the verified
parse, review H-76), so the entry that holds a trusted record is *the*
entry at that path (`Sorted.holds_oid`): a crafted tree that lists a path
twice is refused instead of letting one checked entry stand for another.

What remains assumed:

* **`CommitStep`** / **`GuardedHistoryStep`**: Git commits the index the
  hook checked (A22), so the next `HEAD` has its entries and its policy
  entries, and an object id names one content (A11).
* **The start of history.** Commits made without the keyed hook
  (`--no-verify`, cherry-pick and rebase, a locked checkout, pulled
  commits, other parties) are outside the induction. A full keyed check
  (`verify-index` of an index holding `HEAD`'s entries), a keyed commit
  that changes the policy, or a keyed audit of the commit `HEAD` names
  establishes the invariant. The keyed `audit` (pre-push, A13) keeps the
  same selection-independent invariant for each commit it checks
  (`keyed_audit_authenticates_commit`, below), so an audited `HEAD`
  discharges the start (`audited_head_starts_keyed_history`), relative to
  the audit's own contracts and its start: the parent of the first audited
  commit when it lies outside the range (an audit from the root trusts
  nothing). A local history that was never audited is still trusted by the
  incremental hook in that checkout (tested, with the pre-push refusal:
  `local_attribute_overrides_never_admit_a_forged_record_through_checked_history`).

### The keyed audit of one commit (`Audit.lean`)

`audit_commit` checks one commit against its first parent: the entries
`diff-tree` lists, or the whole tree for a root commit, a config change or
an attribute change. Each examined entry is checked by the extracted
`audit_check` (`audit_check_spec`), which chooses a check in the hook's
vocabulary, and the extracted `staged_verdict`; the model `auditPlan` only
sequences the two. With the key a selected entry is authenticated; an
unprotected file the parent holds exactly is trusted from the parent only
while the config is unchanged (`AuditBase.Parent`); any other unprotected
file is authenticated if it is a record of the commit's config.

* `keyed_audit_authenticates_commit`: if the keyed audit accepted, the
  commit's records authenticate (`RecordsAuthentic`) given its parent's
  when it trusted the parent (nothing for `AuditBase.Tree`), and every
  path the commit's attributes select, metadata aside, is a regular file
  whose record authenticates there (`SelectionAuthentic`), given the
  parent's selection and its agreement on unexamined entries.
* `keyless_audit_checks_envelopes`: without the key, every examined
  selected entry has the envelope and is held by the parent or is no blob
  of a path the commit deleted; nothing is authenticated (A14).
* `audited_head_starts_keyed_history`, `audited_head_keyed_history_authenticated`:
  an audited `HEAD` (with a true guard of the next hook run, which keeps
  `HEAD`'s configuration, `config_of_guard_head`) is the start of
  `keyed_history_authenticated_by_guard`.
* `keyed_audit_chain_authenticated`: a chain of keyed audits, each commit's
  first parent the previous commit, keeps both invariants.

Its contracts: `AuditContracts` (every non-reserved entry not examined is
the parent's exactly, and only while the config is unchanged; the facts
`audit_check` receives and the blobs read are Git's: A20, A19, A11, A21),
`AuditAnswers` (A4), `AuditSelectionAgrees` (A19: the adapter examines the
whole tree when an attribute file changes) and `Realizes` (A5). The
adapter's per-run cache of checked records (`settled_by_cache`) is
reviewed and tested, not modelled.

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
| `HEAD` and `HEAD^1` hold the entry's exact record | `held_records` (`held_records_spec`; binary search, `find_entry_spec`, `same_record_spec`) | `∈`, `Settled` |
| The keyless move check | `blob_elsewhere` (`blob_elsewhere_spec`), through object orders checked by `object_order_ok` (`object_order_ok_spec`) | `BlobElsewhere` |
| How each index entry is checked (protected: authenticated, or the envelope with or without the move check; unprotected: no record, authenticated if a record, or nothing) | `staged_check` (`staged_check_spec`, over `entry_check_spec`), `reads_blob` (`reads_blob_spec`) | `StagedCheckOf` |
| Whether the entry passes, from the blob and the adapter's answers | `staged_verdict` (`staged_verdict_ok`) | `VerdictOk` |
| Each protected blob authenticates at its path | `open_record` (`open_record_spec`), through the `opens` answer (`HookAnswers`, `hook_opens`) | `OpensTo` |
| Without the key: the envelope | `record_envelope_ok` (`record_envelope_ok_spec`) | `EnvelopeOk` |
| Object replies are for the requested id and announced size | `parse_batch_header`, `blob_read` (`parse_batch_header_spec`, `blob_read_spec`) | `BatchHeader`, `blobReadSpec` |

`hookPlan` is the loop in `transcrypt_rs::lifecycle::check_staged`: each
iteration (`hookEntry`) is exactly the generated `staged_check` followed by
the generated `staged_verdict`; it decides nothing itself. That the Rust loop
visits every entry with these calls, reads the blob when `reads_blob` says
so, and answers the verdict's questions truthfully (`HookAnswers`) is what
remains of A4 here (reviewed, tested).

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
**A5**). Since 2026-11-02 the core also builds the primitives:
`unlock_stored_key_spec` proves that `unlock_stored_key` returns
primitives only in that case, and that they are the key schedule's
primitives for exactly the file's last 64 bytes, returned with the
configuration they authenticated; the adapter keeps both in a
`ValidatedKey`, the only interface that seals or opens files. What remains
assumed is the key schedule (`KeyScheduleRealizes`: `Keyed::from_key(k)`
realizes the suite of the bytes `k`, **A5**/**A17**), the file I/O, and the
integrity of the key's CTR half, which config authentication does not
check (**A17**).

## The product theorems (`ProductSecurity.lean`)

The theorems above are restated, and composed, as a short portfolio over
named predicates; each keeps its external hypotheses visible.

| Guarantee | Theorem | What it composes |
| --- | --- | --- |
| A. Authenticated publication | `keyed_publication_authenticates`: `HookContracts`, `Realizes`, `ConfigCommitted` and an accepted keyed check (`KeyedCheckAccepted` in a `CheckMode`) give `AuthenticatedIndex`; `HeadAuthentic` is needed only for an incremental check | `hook_full_check_authenticates` (new), `hook_accepts_only_authenticated_ciphertext_given_history` |
| Check modes | `pre_commit_check_modes` | Theorem 1 in each mode |
| Record invariant | `keyed_check_records_authentic`: an accepted keyed check keeps `RecordsAuthentic` (selection-independent), trusting `HEAD`'s only under the guard | `hook_records_authentic`, `hook_authenticated_of_records` |
| A24 history | `keyed_history_authenticated_by_guard` (no policy or selection hypothesis) | the above, by induction; `records_authentic_of_checked_commit`, `config_unchanged_of_guard`, `hook_policy_guard`, `policy_unchanged_sound` |
| Audited history (A13, the start of A24) | `keyed_audit_authenticates_commit`, `audited_head_keyed_history_authenticated`, `keyed_audit_chain_authenticated` (`Audit.lean`) | `audit_check_spec`, `staged_verdict_ok`, `audit_entry_checked`, `config_of_guard_head`, `keyed_history_authenticated_by_guard` |
| B. Authenticated recovery | `checkout_releases_only_authenticated_plaintext`: smudge's output either differs from the stored record and is exactly the plaintext it authenticates to at that path and configuration, or is the record itself, unchanged, with the v3 envelope (locked, another configuration, private mode); a record it decided to open that does not authenticate is refused. `checkout_opens_genuine_records`: a genuine record of this configuration opens to its plaintext | `smudgeModel_spec`, `smudge_action_spec`, `open_record_complete`, `opensTo_envelopeOk`, `sealed_length` |
| C. No laundering | `repair_never_launders`: seals only the user's change or forced plaintext (no v3 header); rebinds only the user's record that authenticates at its move source; content imported from `HEAD` or an incoming commit is never rebound, and sealed only when `protect` forced it; the user's change is never skipped | `hook_repairs_only_local_changes`, `hook_skips_only_unrepairable`, `repair_plan_repairs_only_local`, `UserStaged.not_committed` |
| D. Configuration-bound key | `stored_key_binds_file_operations`: when the stored key is used (the verified `unlock_stored_key` returned primitives and a config), its file holds the current configuration, the primitives are those of the file's key bytes (`KeyScheduleRealizes`, A5/A17) and authenticate it, and every record they open or seal is bound to that configuration and path | `unlock_stored_key_spec`, `authenticate_key_spec`, `open_record_spec`, `seal_record_spec`, `seal_opens` |

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
| `run : HookEvidence g E`, `hookPlan … = ok true`, `HookAnswers` (the three answers to `staged_verdict`); `RepairContracts` (Theorem 2: `provenance`, `decision`, and `record`, what each reported `RecordClass` means, `RecordEvidence`) | the adapter called the verified functions on these inputs, reports its evidence about each blob truthfully and acted on their results | A4 | REVIEWED + TESTED; the functions PROVED |
| Git commits `g.index` | the commit is the index the hook checked last | A22 (refines A7) | TESTED (every pre-commit test) |
| `RepairContracts.incoming`, `.lazy` (Theorem 2) | the incoming commits are those named by the sequencing state | A23 | TESTED (merge, octopus, cherry-pick, rebase suites) |
| `HeadAuthentic` (corollary; only for an incremental check) | `HEAD`'s selected entries authenticate | A24 (selection form) | REVIEWED + TESTED (keyed audit, A13) |
| `RecordsAuthentic … g.head` (only when the check trusted `HEAD`) | `HEAD`'s records authenticate at their paths, whatever selects them | A24 | induction PROVED (model) (`keyed_history_authenticated_by_guard`); its start PROVED (model) from a keyed audit of `HEAD` (`audited_head_starts_keyed_history`), or a full keyed check or a policy change (TESTED: `local_attribute_overrides_*`, `newly_protected_files_are_authenticated_by_the_hook`, `trees_listing_a_path_twice_are_refused`, `the_keyed_audit_authenticates_records_at_unprotected_paths`) |
| `AuditContracts`, `AuditAnswers`, `AuditSelectionAgrees` (audit) | the audit examined what Git lists, every other entry is the parent's, its facts and answers are true, and an unexamined entry is selected as in the parent | A20, A19, A11, A21, A4 | REVIEWED + TESTED (`audits_read_no_unchanged_unprotected_file`, `the_audit_*`) |
| the audit's parent records (when it trusted the parent) | the first audited commit's parent outside the range has authentic records | A13 | deployment: audited when pushed, or an audit from the root |
| `CommitStep`, `GuardedHistoryStep` (history) | the next `HEAD` is made from the checked index and has its policy entries; objects keep their content | A22, A11 | TESTED; ASSUMED |
| Unforgeability | only the key holder makes records that authenticate | A10 | ASSUMED (standard) |

## What is proved, tested and trusted

* **PROVED (source-derived):** every decision listed in the tables above;
  all are theorems about the generated translation of the production core
  (the 161 theorems of the ledger `proofs/aeneas/v3/PROOF-STATUS.md`,
  standard axioms only:
  `bash proofs/aeneas/check-v3-axioms.sh`).
* **PROVED (model):** the per-entry composition `hook_entry_checked` and
  the end-to-end theorems (with the A24 corollaries), the product theorems
  and the A24 induction (`ProductSecurity.lean`), and the keyed audit of
  one commit with the start of a keyed history (`Audit.lean`), about Lean
  models that only sequence the generated functions.
* **TESTED:** that the Rust adapter matches the models and contracts
  (A4), Git's behavior (A7, A19–A23), the primitives (A5, A9); the
  discharge of A24 by the hook and the audit (also REVIEWED).
* **TRUSTED:** Lean and the Charon/Aeneas translation (A3), Git's object
  identity (A11), cryptographic hardness (A10).

## What the statement does not cover

* **Commits made without the hook** (`--no-verify`, a clone that never ran
  `unlock`, merges that skip `pre-commit`): the `pre-push` hook and
  `audit` check history (A13); what a keyed audit establishes is stated
  in `Audit.lean` (above), relative to its deployment.
* **Keyless forgery:** without the key, only the envelope is checked
  (A14); the next unlocked check or keyed audit authenticates.
* **Unprotected files:** the record checks of unprotected entries (no
  record moved to an unprotected name; with the key, a record `HEAD` holds
  there opens) are the core's `staged_check` and `staged_verdict` and keep
  A24. The refusal of a file that lost its protection to another named
  filter (`check_drift`) is adapter code, tested to match `audit`; it is not
  needed for the promise about selected paths.
* **Local privacy:** smudge, hydrate, lock and the private mode have their
  own lifecycle theorems (`smudgeModel_spec`, `hydratePlan_spec`,
  `lockEntry_spec`); workstation privacy is an optional mode (charter).

## Re-checking

```bash
bash proofs/aeneas/build-v3-tracked.sh
bash proofs/aeneas/check-v3-axioms.sh
cd rust && cargo test --workspace
```
