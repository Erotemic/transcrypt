# Transcrypt v3: the end-to-end security argument

**Written 2026-10-26.** This document states, in one place, what the
machine-checked proofs say about the product's main promise and exactly
which assumptions that statement rests on. It is the readable companion of
[`EndToEnd.lean`](../../proofs/aeneas/v3/V3Wire/Verification/EndToEnd.lean).
Assumption IDs refer to the [assumption register](V3-ASSUMPTIONS.md);
evidence levels follow the [proof ledger](V3-PROOF-COVERAGE.md) (PROVED is
never used for TESTED or REVIEWED evidence).

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
> * Git printed the index, `HEAD` and `HEAD^1` listings exactly (**A20**);
> * Git's `check-attr --cached` answer gives each index path's effective
>   `filter` value under the committed attributes (**A19**);
> * each blob the hook checked is the content of its entry's object id
>   (**A11**, **A21**);
> * the cryptographic primitives realize the abstract AES-SIV suite `σ`,
>   whose truncated SHA-256 is the configuration id (**A5**);
> * the configuration used is the one staged as `.transcrypt/config`
>   (checked by the adapter, **A4**);
> * the adapter acted only on the verified core's results, as listed in
>   `HookRun`, and its per-entry check is at least as strict as the model
>   `hookEntry` (**A4**).
>
> If the hook accepted, then every entry of the index whose path the
> committed attributes select is a **regular file** (not a symlink or
> submodule), **not reserved metadata**, and its blob:
>
> * **unlocked:** authenticates at exactly that path under the committed
>   configuration (`OpensTo σ config path blob pt`); in the incremental
>   pre-commit hook an entry unchanged since both `HEAD` and `HEAD^1` may
>   instead carry the v3 envelope of that configuration (it was
>   authenticated when it was committed, and `audit` authenticates history);
> * **locked:** has the v3 envelope of that configuration, and is either
>   unchanged since `HEAD` and `HEAD^1` or is not the blob of another path
>   (no record moved without the key).
>
> Git then commits that index (**A22**).

Together with AES-SIV unforgeability (**A10**), "authenticates at that path
under the committed configuration" means the blob is ciphertext produced
with the repository key for that path; `opensTo_unique` makes the plaintext
unique.

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
| Unchanged since `HEAD` and `HEAD^1` | `held_entries` (`held_entries_spec`) | `Holds`, `Settled` |
| The keyless move check | `blob_elsewhere` (`blob_elsewhere_spec`) | `BlobElsewhere` |
| Each protected blob authenticates at its path | `open_record` (`open_record_spec`), in the model `hookPlan` (`hookPlan_spec`) | `OpensTo` |
| Without the key: the envelope | `record_envelope_ok` (`record_envelope_ok_spec`) | `EnvelopeOk` |
| Object replies are for the requested id and announced size | `parse_batch_header`, `blob_read` (`parse_batch_header_spec`, `blob_read_spec`) | `BatchHeader`, `blobReadSpec` |

`hookPlan` is a small Lean model of the loop in
`transcrypt_v3::lifecycle::check_staged` (like the existing `verifyPlan`);
it calls the generated functions. That the Rust loop matches it is part of
A4 (reviewed, tested).

## Theorem 2: the hook repairs only local changes

`hook_repairs_only_local_changes`, in prose:

> For a protected index entry, suppose the hook computed the inputs of the
> verified decision `seal_action` with the verified core: membership in
> `HEAD` and in the commits being merged, picked, reverted or rebased
> (`held_entries`; those commits are consulted only when some protected
> entry changed), the local-change input (`is_local_change`), whether the
> blob opens at its own path (`open_record`), whether it has the v3 header
> (`parse_file_header`) and, for a move, a source from `next_move_source` at
> which it opens. Assume Git's listings are exact (**A20**) and the
> sequencing state names the commits being brought in (**A23**). If
> `seal_action` decided to seal or re-seal the entry, then:
>
> * it is a **local change** (`LocalChange`): neither `HEAD` nor any
>   incoming commit holds that blob at that path (and the incoming commits
>   are known), unless `protect` forced sealing a plaintext;
> * it did not already authenticate at its path;
> * only plaintext (no v3 header) is sealed;
> * a rebind re-encrypts exactly the plaintext of a record that
>   authenticates at a `HEAD` path it was moved from (`MoveSource`: same
>   blob, another path, whose own entry has left the index).

So content that arrives in a commit is only ever checked by Theorem 1,
never repaired: a hostile commit that moves a record or adds plaintext is
refused, not laundered (`sealSpec_repairs_only_local`, now with the inputs
proved).

## Theorem 3: the key is the one for this configuration

`stored_key_authenticates_current_config`: `Key::load` uses a stored key
only when the verified `stored_key_state` says `Unlocked`. Then the key
file holds exactly the current configuration followed by the key, and the
key authenticates that configuration (`ConfigAuthentic`, relative to
**A5**). The adapter builds the primitives from the file's key bytes
(**A17**).

## Hypotheses and where they are discharged

| Hypothesis in Lean | Meaning | Assumption | Evidence |
| --- | --- | --- | --- |
| `GitListing index g.index` (and `HEAD`, `HEAD^1`, incoming) | Git's listing is exactly its snapshot | A20 (refines A7) | TESTED (real Git, all lifecycle suites); the parse itself PROVED |
| `GitAttributes g response` | `check-attr --cached` reports the committed attributes | A19 | TESTED (Git 2.43, CI 2.34); the parse PROVED |
| `GitObject g oid record` | bytes read by id are that object | A11, A21 | header and size decision PROVED; reading exactly the size and the LF TESTED; object identity ASSUMED (Git's hash) |
| `Realizes inst prims σ` | the primitives compute AES-SIV / SHA-256 | A5 (with A9) | TESTED (vectors, differential) |
| `hid : wireBytes id = σ.digest16 config` | the configuration id is the suite's digest | A5 | TESTED (vectors) |
| `hcfg` | the configuration used is the staged `.transcrypt/config` | A4 | REVIEWED + TESTED (`check_staged` compares the staged blob with it) |
| `HookRun …`, `hookPlan … = ok true` | the adapter called the verified functions on these inputs and acted on their results | A4 | REVIEWED + TESTED; the functions PROVED |
| Git commits `g.index` | the commit is the index the hook checked last | A22 (refines A7) | TESTED (every pre-commit test) |
| `hknown`, `hlazy` (Theorem 2) | the incoming commits are those named by the sequencing state | A23 | TESTED (merge, cherry-pick, rebase suites) |
| Unforgeability | only the key holder makes records that authenticate | A10 | ASSUMED (standard) |

## What is proved, tested and trusted

* **PROVED (source-derived):** every decision listed in the tables above;
  all are theorems about the generated translation of the production core
  (60 headline theorems, standard axioms only:
  `bash proofs/aeneas/check-v3-axioms.sh`).
* **PROVED (model):** the composition `hookPlan_spec` and the three
  end-to-end theorems, about Lean models that call the generated functions.
* **TESTED:** that the Rust adapter matches the models and contracts
  (A4), Git's behavior (A7, A19–A23), the primitives (A5, A9).
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
