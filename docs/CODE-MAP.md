# Reading the transcrypt-rs code

A map to read before opening `lifecycle.rs`. The design: every
security-relevant decision is a pure function in the verified core, and the
adapter around it only gathers evidence, asks the core and applies the
answer. What the proofs cover, and what they assume about Git, the OS and the
cryptography, is in [V3-PROOF-COVERAGE](verification/V3-PROOF-COVERAGE.md)
and [V3-ASSUMPTIONS](verification/V3-ASSUMPTIONS.md).

## Layout

| Where | What |
| --- | --- |
| `rust/crates/transcrypt-v3-core/src/lib.rs` | The verified core: `no_std`, no I/O. Parsers of Git's output, the wire format, and every decision. It is extracted to Lean by Aeneas, so it is written in a restricted style (no `?`, explicit loops); do not "modernize" it. Its unit tests are in `tests.rs` (not extracted). |
| `rust/crates/transcrypt-rs/src/lib.rs` | `Keyed`: Argon2id and AES-256-SIV (RustCrypto) behind the primitive contract the core assumes (A5). |
| `rust/crates/transcrypt-rs/src/main.rs` | The executable: command dispatch and the passphrase; `cli.rs` parses the command line into a `Command` holding exactly each command's arguments. |
| `lifecycle.rs` | The pre-commit hook and `verify-index`, `hydrate`, `lock`. |
| `filter.rs`, `process.rs` | Git's clean and smudge filters, per file or as one long-running process. |
| `git/` | The `Repository` a command works on (its root and Git directories, found once by `Repository::discover` and passed to everything that needs them, and its object reader) and every Git subprocess, bounded (`mod.rs`), with replies parsed by the core: object reads (`objects.rs`), index and tree listings and diffs (`listings.rs`), index updates (`index.rs`), attribute queries (`checkattr.rs`). |
| `listing.rs` | `Listing` and `OrderedListing`: a snapshot's bytes and record ends, passed to the core only through their methods. |
| `credential.rs`, `session.rs` | The stored key, and the private-mode agent. |
| `worktree.rs`, `fsat*.rs`, `os_*.rs` | Writing worktree files safely (directory-relative, never following links), privacy, and the per-OS primitives (A8, A25). |
| `setup.rs`, `attributes.rs`, `rekey.rs`, `migrate.rs`, `audit.rs`, `merge.rs`, `diff.rs` | Everything else the commands do. |
| `proofs/aeneas/v3/V3Wire/Extraction/` | The core translated to Lean (generated; never edited). |
| `proofs/aeneas/v3/V3Wire/Verification/` | Proofs that the generated code meets the specification, and the end-to-end theorems. |
| `proofs/lean/Transcrypt/V3Policy.lean` | The independent specification: an umbrella over `V3Policy/` (`Constants`, `Paths`, `Authentication`, `Lifecycle`, `Git`, `Credentials`), with the wire format in `V3Wire.lean` and `V3WireCodec.lean`. |

## One commit, start to finish

1. Git runs the `pre-commit` hook, which runs `transcrypt-rs pre-commit`
   calls `lifecycle::verify(repo, true)`.
2. **Evidence.** `Snapshot::read` takes one exact index listing, and the
   attributes Git reports for those paths, both parsed by the core. Then come
   `HEAD`'s listing (`commit_listing`) and the commits a merge or rebase is
   bringing in (`incoming`; "unknown" whenever Git's sequencing state is not
   certain).
3. **Decision.** For each protected entry, `seal_snapshot` asks the core
   where its content came from (`entry_provenance`: a `Provenance`,
   committed, local, forced by `protect`, or unknown) and whether its blob
   matters (`needs_record`); only then does it read the blob and find what
   it is (`classify`: a `RecordClass`, opens here, plaintext, moved from a
   `HEAD` record, or unusable). The core's `repair_plan` decides from the
   two (keep, seal plaintext the user staged, re-encrypt a renamed record,
   or leave it to the check).
4. **Effect.** The new records go into the index in one `IndexUpdate`, which
   reads the index back to confirm every entry was staged exactly.
5. **Check.** `check_index` re-reads the final index and requires every
   protected entry to be a record that authenticates at its path with the
   key (or, locked, at least has the envelope), as `entry_check` decides. Git then commits that index
   (A22).

## Authenticated versus keyless

With the key, a record is accepted only if it **opens**: `open_record`
authenticates the config and the exact path. Without it (a locked checkout,
`audit` on a server), only the **envelope** is checked
(`record_envelope_ok`: size, header, config id; `is_record` decides it
from a blob's size and first `ENVELOPE_PREFIX_LEN` bytes without loading the
rest). That stops plaintext, not a
forged record (A14). Function and message names say which of the two
happened.

## Decisions and their proofs

What kind of evidence each step has (column **Kind**):

* **S, source-derived:** the step is a core function extracted from
  `lib.rs` by Aeneas, and the theorem is about that generated code.
* **M, Lean model:** the theorem is about a handwritten Lean model of the
  adapter's sequencing (`hookPlan`, `hydratePlan`, `lockEntry`,
  `verifyPlan`, and the end-to-end theorems over `HookEvidence` and
  `RepairInputs`). The model calls the generated functions, but that the
  Rust loop matches it is assumption A4. For the repairs the model is only
  the evidence: what each `RecordClass` the adapter reports means
  (`RecordEvidence`); the decisions are the generated functions.
* **T, adapter, tests only:** Rust in `transcrypt-rs` with no Lean
  statement; covered by the tests in `rust/crates/transcrypt-rs/tests`
  and review.

| Adapter step | Kind | Core function | Theorem (proofs/aeneas/v3/V3Wire/Verification) |
| --- | --- | --- | --- |
| Parse the index or a tree listing | S | `parse_listing`, `listing_fields` | `parse_listing_spec`, `listing_fields_spec` (SnapshotOrder, SnapshotListing) |
| Parse the attributes Git reports | S | `parse_listing_attrs` | `parse_listing_attrs_spec` (SnapshotAttrs) |
| Is an entry held by `HEAD` or an incoming commit | S | `held_entries` | `held_entries_spec` (SnapshotLookup) |
| Where a staged entry's content came from (`Provenance`) | S | `entry_provenance`, `provenance_of` | `entry_provenance_spec`, `provenance_of_spec` (SnapshotLookup) |
| Whether its blob is read at all | S | `needs_record` | `needs_record_spec`, `needs_record_skip` (Bytes) |
| Keep, seal, re-encrypt or leave it (`RepairPlan`) | S | `repair_plan` | `repair_plan_spec`, `repair_plan_repairs_only_local`, `repairSpec_repairs_only_local` (Bytes) |
| Which check each index entry gets (`check_staged`): protected, authenticate or (keyless or settled) the envelope; unprotected, no record if staged since `HEAD`, authenticated if a record when `HEAD` is not trusted | S | `staged_check` (over `entry_check`), `reads_blob` | `staged_check_spec`, `reads_blob_spec`, `entry_check_spec` (Staged, Bytes) |
| Whether it passes, asking the adapter (`EntryEvidence`) only what the check needs | S | `staged_verdict` (generic over `StagedEvidence`) | `staged_verdict_ok` (Staged); laziness in `staged_verdicts_accept_only_what_their_check_requires` (core tests) |
| Does `HEAD` (or `HEAD^1`) hold an entry's exact record | S | `held_records` | `held_records_spec` (Staged) |
| `HEAD` is trusted only while no attribute file and not the config changed since `HEAD` and `HEAD^1` (A24) | S | `policy_unchanged` (over `is_policy_path`, `is_attributes_path`), with `held_records` | `policy_unchanged_spec`, `policy_unchanged_sound` (SnapshotPolicy); `hook_policy_guard`, `config_unchanged_of_guard` (EndToEnd, ProductSecurity); `settled_entries_are_authenticated_after_*`, `newly_protected_files_are_authenticated_by_the_hook`, `local_attribute_overrides_*`, `ordinary_commits_read_no_unchanged_unprotected_file` (`adversarial.rs`) |
| Where a renamed record came from | S | `next_move_source` | `next_move_source_spec` (SnapshotMoves) |
| Encrypt, decrypt | S | `seal_record`, `open_record` | `seal_record_spec`, `open_record_spec` (Protocol) |
| Keyless check of a record (`is_record` reads only its size and first bytes) | S | `record_envelope_ok`, `record_envelope_prefix_ok` | `record_envelope_ok_spec`, `record_envelope_prefix_ok_spec`, `record_envelope_prefix_ok_record` (Envelope) |
| What smudge does with a blob | S | `smudge_action` | `smudge_action_spec` (Envelope) |
| Read one object from `cat-file --batch` | S | `parse_batch_header`, `blob_read` | `parse_batch_header_spec`, `blob_read_spec` (Objects) |
| Use the stored key | S | `stored_key_state` | `stored_key_state_spec` (Objects) |
| Hydrate or lock a file | S | `hydrate_action`, `lock_action` | `hydrate_action_spec`, `lock_action_spec` (Bytes) |
| Hydrate, lock and `verify-index` over all protected files | M | the rows above | `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` (Lifecycle) |
| The hook's final check, as a whole (a loop over `staged_check` and `staged_verdict`) | M | the rows above | `hook_entry_checked`, `hook_accepts_only_authenticated_ciphertext`, `hook_records_authentic` (EndToEnd) |
| The hook's repairs, as a whole | M | the rows above | `hook_provenance`, `hook_skips_only_unrepairable`, `hook_repairs_only_local_changes` (EndToEnd) |
| The product statements and the A24 history over keyed commits | M | the rows above | `keyed_publication_authenticates`, `pre_commit_check_modes`, `keyed_check_records_authentic`, `keyed_history_authenticated_by_guard` (with `records_authentic_of_checked_commit`, `config_unchanged_of_guard`), `checkout_releases_only_authenticated_plaintext`, `repair_never_launders`, `stored_key_binds_file_operations` (ProductSecurity) |
| Unprotected staged entries: no record handed to another filter (`check_drift`) | T | `record_envelope_prefix_ok` (S) per blob | none; tests in `workflows.rs` (`git lfs track`) |
| Enumerate and flush or check the other worktrees in `lock` (`other_worktrees`, `others_encrypted`) | T | none | none; tests in `workflows.rs`, `adversarial.rs` (linked worktrees) |

An S or M row means the adapter calls those functions and acts on their answers. The
adapter code itself is not proved: its correspondence to the Lean models is
assumption A4, checked by the tests in `rust/crates/transcrypt-rs/tests`.
