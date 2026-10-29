# Transcrypt v3: proof and test coverage ledger

**Updated 2026-10-26.** This ledger keeps a compiled proof, a functional
regression, an extraction check and a cryptographic assumption from being
reported as the same kind of evidence. See the active
[v3 roadmap](V3-ROADMAP.md), the theorem-level
[proof status](../../proofs/aeneas/v3/PROOF-STATUS.md) and the
[trust-ordered assumption register](V3-ASSUMPTIONS.md), and the
[maintainer's product charter](V3-PRODUCT-CHARTER.md). The proofs are about
the current source: attribute-based selection with a suffix-free path policy.
Where the key is stored is adapter code; the decision to use it is proved
(`stored_key_state_spec`, A17). The end-to-end statement and its
hypotheses are in [V3-SECURITY-ARGUMENT](V3-SECURITY-ARGUMENT.md).

Evidence levels:

- **PROVED (source-derived):** a compiled Lean theorem explicitly names a
  Charon/Aeneas-generated production Rust function in its proposition.
- **PROVED (model):** compiled theorem about a Lean model of adapter
  sequencing that calls generated production functions.
- **SPEC PROVED:** compiled theorem about the independent Lean model only.
- **TESTED:** real Rust/Git tests or independent reference tests.
- **GENERATED:** extraction/snapshot integrity and compilation; this does not
  imply functional refinement.
- **TRUSTED / REVIEW:** external operation or security property outside Lean.
- **OPEN:** no sufficient evidence yet.

| ID | Requirement | Evidence | Remaining |
| --- | --- | --- | --- |
| W-00 | Generated Lean matches the Rust core source | **GENERATED**: `SNAPSHOT.json`, source-hash gate, CI regeneration with pinned cargo-hax 0.4.2 (reproduced locally byte-for-byte) | Maintain on every core change |
| W-01 | Magic/version markers match the spec | **PROVED** `extracted_*_magic_matches_spec`, `extracted_magic_disjoint` | — |
| W-02 | Config encoder writes all 55 bytes | **PROVED** `encode_config_bytes`, `encode_config_refines` | — |
| W-03 | Exact config decoder accepts iff magic correct, fields exact | **PROVED** `decode_config_exact_spec`, roundtrip `decode_config_exact_encode_config` | — |
| W-04 | File-header encoder writes all 22 bytes | **PROVED** `encode_file_header_bytes`, `encode_file_header_refines` | — |
| W-05 | File-header decoder rejects wrong magic, extracts id | **PROVED** `decode_file_header_exact_spec` + roundtrip | — |
| W-06 | Public slice parsers enforce length and magic | **PROVED** `parse_config_spec`, `parse_file_header_spec` (exactly the spec's shape decoders) | — |
| P-02 | Git index records select the authenticated path bytes and regular-mode check | **PROVED** `parse_index_entry_spec` (exactly the spec's `IndexRecord`); whole listings `parse_listing_spec` (exactly `listingBytes` of well-formed entries in Git's byte order of paths, each path once (`Sorted`), both directions; `bytes_lt_spec` = spec `BytesLt`) and each entry's fields `listing_fields_spec` (the adapter builds its entries from them) | Git prints the listing (A20); `ls-tree` records are rewritten by the adapter (A20) |
| P-03 | Git objects are read only by plain object ids from one snapshot, and the bytes are that object's | **PROVED** `is_object_id_spec`, `objectId_plain`, `indexRecord_oid`; reply header `parse_batch_header_spec` (exactly `<oid> blob <size> LF`, canonical decimal, unique size `batchHeader_unique`) and read decision `blob_read_spec`; **TESTED** revision-syntax and pathspec-magic filenames (`adversarial.rs`), reply fuzzing | Reading exactly the announced bytes (A21); object identity (A11) |
| P-04 | Git filter-protocol framing | **PROVED** `decode_pkt_len_spec` (exactly `PktLenAccepted`); **TESTED** `long_running_filter_protocol` | Key/value lines and chunking are adapter code (A4) |
| G-06 | No plaintext reaches a remote from commits that skipped `pre-commit` | **PROVED** `record_envelope_ok_spec`, `opensTo_envelopeOk` (keyless check accepts every genuine record), `record_envelope_prefix_ok_record` (the size and first `FILE_MIN_LEN` bytes decide it, so `is_record` skips the rest of the blob); **TESTED** `pre-push` refusal, keyless `audit` in a never-unlocked clone and a bare repository | Deployment of the hook or a server-side audit (A13); forged envelopes (A14) |
| P-01 | Canonical path policy: any canonical Git path except reserved metadata (`.transcrypt/…`, `.gitattributes`, `.gitmodules`) | **PROVED** `is_canonical_protected_path_spec` = spec `CanonicalProtectedPath` (via `List.splitOn`), `is_reserved_path_spec` = spec `Reserved`, with `matches_at_spec`, `ends_with_spec` | — |
| P-05 | Protected-file selection: Git's attribute answers are parsed exactly | **PROVED** `parse_attr_record_spec` (accepts exactly the spec's `AttrRecordAt` for the requested path, both directions; `protected` iff the value is `transcrypt-v3`), `find_byte_spec`; **SPEC PROVED** `attrRecordAt_unique`; **PROVED** `parse_attr_response_spec`, `parse_attr_response_complete` (path lists); for the index `parse_listing_attrs_spec` (the answer checked against the listing's own paths, both directions) and `first_unselectable_spec` (`Selectable`); **TESTED** `arbitrary_patterns_protect_exactly_the_selected_files` | Git's attribute evaluation (A19) |
| C-01 | Deterministic Argon2id + AES-SIV bytes match independent vectors | **TESTED** `tests/v3/reference/check_vectors.py`, Rust vector tests; differential corpus vs OpenSSL AES-SIV and reference Argon2id (`differential.py`, `v3_differential.rs`: 22 lengths, raw-byte paths, exhaustive tampering/truncation/extension/context changes) | External review (R-01) |
| C-02 | Config authenticated; ordered path-bound AD; no plaintext without authentication | **PROVED** `authenticate_config_spec`, `seal_record_spec`, `open_record_spec`, `open_record_complete` relative to `Realizes`; **TESTED** `keyed_satisfies_the_realizes_contract` for the production primitive | AES-SIV security (A10) |
| C-03 | Agent performs only authorized operations under the authenticated config | **PROVED** `authorize_agent_request_spec`, request framing `decode_frame_header_encode`; **TESTED** hostile-client suite | Same-UID boundary (A6) |
| G-01 | init/clone/unlock/hydrate/clean/commit/lock/re-unlock | **TESTED** `git_lifecycle.rs` | — |
| G-02 | Staged index verified (not HEAD); selection by staged attributes; no transplant | **PROVED (model)** `verifyPlan_spec`, `hookPlan_spec`, `hook_accepts_only_authenticated_ciphertext` (see E2E-01); **PROVED** `entry_check_spec` (how each protected entry is checked: authenticated, or envelope with or without the move check), `parse_listing_spec`, `parse_listing_attrs_spec`, `first_unselectable_spec`, `held_entries_spec` (binary search, `find_entry_spec`), `blob_elsewhere_spec` (through `object_order_ok_spec`), `parse_index_entry_spec` (`100644`/`100755` only); **TESTED** nested-attribute, blob-swap, hostile-move, foreign-repository, truncated/extended record, duplicate-path tree (`trees_listing_a_path_twice_are_refused`) tests, linear-time lookups (`snapshot_queries_scale_to_large_listings`) | Git semantics (A7, A19, A20, A22); the adapter follows the model (A4) |
| G-03 | Crash safety of multi-file operations | **PROVED (model)** hydrate decides every file before writing (all-or-nothing on errors) and replaces a worktree file only if it is exactly an authentic record at its path, by exactly that record's plaintext (`hydratePlan_spec`); lock only discards recoverable plaintext (`lockEntry_spec`); **TESTED** SIGKILL fault injection at 12 points of `lock`/`hydrate`, interrupted resume, crash leftovers confined to private staging, stamp-checked replacement, operation lock | Same-UID race window between stamp check and rename (A8, A12) |
| G-04 | Private mode: derived key absent from disk while unlocked | **TESTED / DESIGN** private agent, 0600 socket in 0700 dir, stale-socket tests | Swap/core-dump hardening (A8) |
| G-08 | Private mode: Git never writes plaintext readable by other users | **TESTED** `git_never_writes_plaintext_readable_by_others` (checkout, merge, rebase, stash, restore under `umask 022`/`077`); design in the spec's smudge rule | Git's umask behavior (A15); files users create themselves (A8) |
| G-SM | Smudge never presents non-record bytes as a protected file; opens only its own config's records | **PROVED** `smudge_action_spec` (= spec `smudgeSpec`), `smudgeSpec_keep_envelope`; **PROVED (model)** `smudgeModel_spec` (output is the unchanged envelope or authenticated plaintext); **TESTED** stale-key and old-history checkouts | The adapter follows the model (A4) |
| G-09 | Missing local protection and unprotected remotes are detectable | **TESTED** `doctor_detects_missing_protection`, `remote_enforcement_check_detects_unprotected_remotes` | Deployment (A13) |
| G-05 | Lock never destroys uncommitted plaintext | **PROVED** `lock_action_spec`, **PROVED (model)** `lockEntry_spec` (resealing through the idempotent clean); **TESTED** unstaged-edit refusal, stamp-checked replacement | — |
| G-07 | Clean stores only genuine records; locked filters never emit anything but an unchanged v3 envelope | **PROVED (model)** `cleanModel_spec`, `cleanModel_genuine`, `cleanModel_idempotent`, `lockedFilterModel_spec`; **TESTED** `clean_is_idempotent_and_still_refuses_foreign_records`, locked checkout tests | The adapter follows the models (A4); forged envelopes while locked (A14) |
| G-SEL | Any Git-attribute-selected pathname gets authenticated public-Git ciphertext | **PROVED** P-01, P-05, C-02 for the core; **TESTED** `.env`, directories, `**`, custom globs, quoted and non-UTF-8 names, executables, nested attributes, exclusions, per-commit audit policy (`workflows.rs`) | A16, A19 |
| G-KEY | Stored key is the default, the agent optional, identical v3 bytes in both modes; a key is used only for the config it authenticates | **PROVED** `stored_key_state_spec` (= `storedKeySpec`), `storedKeySpec_unlocked`, `stored_key_authenticates_current_config` (relative to `Realizes`); **TESTED** `assert_unlocked` lifecycle, `stored_key_unlock_needs_no_agent_and_follows_the_umask`, `stored_and_private_modes_encrypt_identically`, `pulled_rekey_makes_the_stored_key_stale_until_unlock`, `legacy_keys_macro_redefinitions_and_crlf` (legacy and damaged files) | File I/O and building the primitives from the file's key (A17); local key access trusted by design |
| G-MV | Normal rename produces an authenticated record for the destination path or a clear recoverable failure; hostile moves are not laundered | **PROVED** `seal_action_spec` with `sealSpec_repairs_only_local` (the hook's decision repairs only local changes), `sealSpec_seal_plain`, `sealSpec_rebind_moved`; the inputs `held_entries_spec`, `is_local_change_spec` (= `LocalChange`), `next_move_source_spec` (= first `MoveSource`); **PROVED (model)** `hook_repairs_only_local_changes`; re-encryption goes through `open_record`/`seal_record` (C-02); **TESTED** `renames_are_re_encrypted_for_their_new_path`, `locked_renames_and_unbound_moves_are_refused`, `merges_are_verified_before_the_merge_commit`, `rename_and_edit_on_two_branches_conflict_in_plaintext`, hostile move in `git_lifecycle` | Git's listings (A20) and sequencing state (A23); the adapter's call sequence (A4) |
| E2E-01 | Selected paths enter Git as authenticated ciphertext (the pre-commit hook) | **PROVED (model)** `hook_accepts_only_authenticated_ciphertext`: if the hook accepted, the index, `HEAD` and `HEAD^1` are sorted (each path once) and every index entry the committed attributes select is `Selectable` and its blob authenticates at exactly its path under the committed config (or, incremental, is settled since `HEAD` and `HEAD^1` with the envelope; locked: envelope and no moved blob); with A24 every selected entry authenticates (`hook_accepts_only_authenticated_ciphertext_given_history`); `hook_repairs_only_local_changes`; `stored_key_authenticates_current_config`. All hypotheses named in [V3-SECURITY-ARGUMENT](V3-SECURITY-ARGUMENT.md); **TESTED** `newly_protected_files_are_authenticated_by_the_hook` (settled only while the attributes are unchanged) | A4 (`HookEvidence`), A5, A10, A11, A19–A24 |
| G-MIG | Explicit recoverable one-time Bash v2 → v3 transition | **TESTED** `bash_v2_repositories_migrate_to_v3` against the real Bash script (refusal of uncommitted work, pattern preservation, fresh-clone unlock); `rewrite_attributes` unit test | Git/OS adapter transaction assumptions; historical v2 risk |
| F-02 | Repository files v3 writes never follow committed symlinks | **TESTED** `rekey_never_writes_through_committed_symlinks`, `protected_parent_symlinks_cannot_redirect_lock_or_hydrate`; design: one writer (`write_repository_file`) | Same-UID races (A8) |
| B-01 | Standalone Bash conforms to v3 | **OPEN / DEFERRED** (V7) | Bash AES-SIV dependency decision |
| R-01 | Independent algorithm, threat and adapter security review | **REVIEW (internal)** [V3-SECURITY-REVIEW.md](V3-SECURITY-REVIEW.md) | External review before security-sensitive release |

## Historical first-core completion gate (achieved; not the product finish line)

- [x] W-02 through W-06 each have a compiled theorem referring to the actual
      extracted Rust function, including the public slice boundary.
- [x] The invoked pure decision seam (path, config binding, seal/open,
      agent authorization, attribute parsing, smudge, hydrate/lock) has proofs naming
      the same functions the running adapter calls (C-02, C-03, G-02, G-05).
- [x] All Rust v3 unit, Git integration, adversarial and independent crypto
      vector tests pass; CI rebuilds the tracked Lean, audits axioms and
      re-extracts for drift; adapter assumptions are documented in the
      assumption register. External review R-01 remains independent of this
      formalization gate.

On each new theorem or material adapter change, update this table and
`proofs/aeneas/v3/PROOF-STATUS.md` in the same commit.

## Interpretation

The allowed claim is: *the production Rust v3 wire codec and protocol
decision core are machine-checked against an independent specification,
including the pre-commit hook's inputs computed from Git's listings, and
the adapter's lifecycle sequencing is proved safe in a Lean model; the
end-to-end statement that selected paths enter Git as authenticated
ciphertext holds assuming the documented cryptographic, Git/OS and adapter
contracts ([V3-SECURITY-ARGUMENT](V3-SECURITY-ARGUMENT.md)).* It is
**not** a claim that Transcrypt v3 is fully formally verified or that
cryptographic security is proved from first principles.
