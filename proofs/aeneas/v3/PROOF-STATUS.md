# Formal verification ledger — production v3 core

**Reconciled 2026-10-26.** Every theorem below is about the Charon/Aeneas
translation of the production `rust/crates/transcrypt-v3-core/src/lib.rs`
(pinned by `SNAPSHOT.json`), stated against the independent specification in
`proofs/lean/Transcrypt/{V3Wire,V3WireCodec,V3Policy}.lean`. All are `WP.spec`
triples, so they also exclude panics (index, overflow) and divergence. The
default `V3Wire` target builds all of them;
`bash proofs/aeneas/check-v3-axioms.sh` confirms that all 100 theorems named in
the table below (listed in `audit/Axioms.lean`) use only `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, `admit`,
`axiom`, `native_decide` or `bv_decide` occurs in any verification module
(enforced by `v3_snapshot.py verify`).

**Correction (2026-10-25).** Until this date the audit script read only the
first line of each `#print axioms` report, and Lean wraps long lists. The two
frame-decoding theorems then depended on `bv_decide`'s native-evaluation
axioms, which the audit did not report. The lemma `be32_bv` is now proved bit
by bit without `bv_decide`, and the script parses complete reports (checked
against a wrapped list containing a native axiom).

For the cross-component picture see
[`V3-PROOF-COVERAGE.md`](../../../docs/verification/V3-PROOF-COVERAGE.md) and
the trust-ordered [`V3-ASSUMPTIONS.md`](../../../docs/verification/V3-ASSUMPTIONS.md).

| Module | Production function(s) | Theorem(s) | Statement (informal) |
| --- | --- | --- | --- |
| `Refinement` | constants | `extracted_{config,file}_magic_matches_spec`, `extracted_magic_disjoint` | Version markers equal the spec and differ |
| `Codec` | `encode_config_prefix`, `encode_config`, `encode_file_header` | `encode_config_prefix_bytes`, `encode_config_bytes`, `encode_file_header_bytes`, `encode_{config,file_header}_refines` | Every output byte, for arbitrary salt/tag/id |
| `Codec` | `decode_config_exact`, `decode_file_header_exact` | `decode_{config,file_header}_exact_spec` | `Ok` iff magic matches (checked with `matches_at`), with exact fields; `Err Magic` iff magic differs; never `Err Length` |
| `Codec` | `parse_config`, `parse_file_header` (public slice boundary) | `parse_config_spec`, `parse_file_header_spec` | Exactly the spec's `decodeConfigShape` / `decodeFileHeaderShape`, with `Length` vs `Magic` classified |
| `Codec` | roundtrips | `decode_config_exact_encode_config`, `decode_file_header_exact_encode_file_header`, `parse_config_encode_config` | Decoding an encoding returns the input |
| `Bytes` | `bytes_eq`, `matches_at`, `find_byte` | `bytes_eq_spec`, `matches_at_spec`, `find_byte_spec` | Equality and prefix-at-offset decisions; the first occurrence of a byte at or after an offset |
| `Bytes` | `hydrate_action`, `lock_action` | `hydrate_action_spec`, `lock_action_spec` | Exactly `hydrateSpec` / `lockSpec` |
| `Path` | `ends_with`, `is_reserved_path`, `component_ok`, `is_canonical_protected_path` | `ends_with_spec`, `is_reserved_path_spec`, `component_ok_spec`, `is_canonical_protected_path_spec` | Suffix decision; exactly the spec's `Reserved` (`.transcrypt/…`, every `.gitattributes`, `.gitmodules`) and `CanonicalProtectedPath` (defined with `List.splitOn`, excludes `Reserved`) |
| `Attr` | `parse_attr_record`, `parse_attr_response` | `parse_attr_record_spec`, `parse_attr_response_spec`, `parse_attr_response_complete` | `Ok` ⇒ the spec's `AttrRecordAt` (`path NUL filter NUL value NUL`) for exactly the requested path at `start`, `next` = its end, `protected` ⇔ `Selected value`; `Err Attribute` ⇒ no such record exists (no preconditions; the length guard is overflow-free). The whole-response parser `parse_attr_response` (called by `git::protected_flags`): if it accepts, `request` is NUL-free paths each NUL-terminated (one per flag), `response` is exactly `attrResponse (paths.zip values)` with NUL-free values, and the output flags are `values.map (decide ∘ Selected)`; conversely, on such a request and Git's answer it accepts with exactly those flags (completeness uses `attrRecordAt_unique`) |
| `Index` | `parse_index_entry` (over `find_byte`, `matches_at`) | `parse_index_entry_spec` | Accepts exactly the spec's `IndexRecord` (stage 0, path after the first TAB, `regular` flag ⇔ mode `100644` or `100755`) and returns that path |
| `Frame` | `encode_be_u32`, `decode_be_u32`, `encode_frame_header`, `decode_frame_header` | `encode_be_u32_spec`, `decode_be_u32_spec`, `encode_frame_header_spec`, `decode_frame_header_spec`, `decode_frame_header_encode` | Agent request header is exactly the spec's `frameHeader`; decoding inverts encoding |
| `Bytes` (repair) | `seal_action` | `seal_action_spec`, `sealSpec_repairs_only_local`, `sealSpec_seal_plain`, `sealSpec_rebind_moved` | The pre-commit repair decision is exactly `sealSpec`: only a local change that does not already open is repaired (no laundering of committed content), only plaintext is sealed, only a moved record is re-sealed |
| `Envelope` | `is_object_id`, `record_envelope_ok`, `smudge_action` | `is_object_id_spec`, `record_envelope_ok_spec`, `smudge_action_spec` | Object ids passed to Git are exactly the spec's `ObjectId` (40/64 lowercase hex: never revision syntax or an option, `objectId_plain`); the keyless check is exactly `EnvelopeOk` (size bound, magic, config id), which every genuine record satisfies (`opensTo_envelopeOk`); the smudge decision is exactly `smudgeSpec` (`Ok Open`/`Ok Keep` ⇔ `some .open_`/`some .keep`; `Err Size`/`Err Foreign` ⇔ `none`, classified) |
| `Pkt` | `decode_pkt_len` | `decode_pkt_len_spec` | Git filter-protocol packet headers: `Ok n` exactly when the header is four lowercase hex digits for a flush (0) or a 5..65520-byte packet (`PktLenAccepted`); otherwise `Err Request` |
| `Protocol` | `initialize_config` | `initialize_config_spec` | Output is the spec layout and authenticates |
| `Protocol` | `authenticate_config` | `authenticate_config_spec` | `Ok` iff `ConfigAuthentic`; refusals classified |
| `Protocol` | `seal_record` | `seal_record_spec` | `Ok` ⇒ `MaySeal` and output = `sealedRecord`; every refusal names a violated precondition or primitive failure |
| `Protocol` | `open_record` | `open_record_spec`, `open_record_complete` | `Ok` ⇒ `OpensTo` for exactly the released bytes; authentication failure ⇒ zeroed buffer and no genuine record exists; other refusals leave the buffer untouched; genuine right-sized records always open to their plaintext |
| `Protocol` | `authorize_agent_request` | `authorize_agent_request_spec` | Exactly `authorizeSpec` |
| `Lifecycle` | adapter sequencing models over the above | `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` | Hydrate replaces a worktree file only if it is exactly an authentic record for its path (the staged one, another, or, for an unmerged path, the merge result), and only by exactly that record's plaintext; any error aborts before writing; lock (resealing with the agent's idempotent clean, `cleanModel`) only discards plaintext the record restores; verify-index success ⇒ every staged record opens at its own path |
| `Filters` | adapter filter models over `open_record`, `seal_record`, `record_envelope_ok`, `smudge_action` | `cleanModel_spec`, `cleanModel_genuine`, `cleanModel_idempotent`, `lockedFilterModel_spec`, `smudgeModel_spec` | Unlocked clean (`clean_file`) stores only genuine records: either the input already opens at this path, or it is sealed under `MaySeal`; a genuine record is returned unchanged (idempotence). The locked filters output only the unchanged input, and only if it has the v3 envelope of the config. Smudge (`smudgeModel`, including the private-mode `keepRecord` path) outputs either the unchanged input, which has the v3 file envelope within the size bound and authenticates at this path whenever `smudgeSpec` decided to open it, or exactly the plaintext it authentically opens to (`OpensTo`) at this path |
| `Snapshot` | `bytes_lt`, `listing_ordered` | `bytes_lt_spec`, `listing_ordered_spec` | Exactly the spec's byte order `BytesLt` (Git's order of paths); whether a listing's paths strictly increase (`Sorted`) or never decrease (`PathOrdered`) |
| `Snapshot` | `parse_listing` (with `record_ok`, `listing_ordered`) | `parse_listing_spec` | Accepts exactly `listingBytes es` of well-formed entries (`EntryOk`: six-byte mode, object id, nonempty path, no NUL) in path order (`unique`: `Sorted`, each path once; otherwise `PathOrdered`), one `ends` slot per record, and records where each ends (`ListingOf`); for any such listing it computes the ends and accepts exactly when the order holds (sound and complete) |
| `Snapshot` | `listing_fields` | `listing_fields_spec`, `FieldsOf.slices` | Record `i`'s offsets delimit exactly its object id and path, and `regular` ⇔ its mode is `100644`/`100755` |
| `Snapshot` | `find_entry` (over `find_path`, `path_before`, `path_at`, `record_is`) | `find_entry_spec` (with `find_path_spec`, `record_is_spec`) | In a listing in path order, a binary search finds a record naming the blob at the path exactly when `Holds` |
| `Snapshot` | `held_entries` (over `find_entry`) | `held_entries_spec` | `held[i]` ⇔ `wanted[i]` and the other listing (in path order) `Holds` entry `i`'s blob at its path |
| `Snapshot` | `is_local_change` | `is_local_change_spec` | Exactly the spec's `LocalChange` (changed since `HEAD`, not in a known incoming commit; or forced plaintext) |
| `Snapshot` | `object_order_ok` (over `object_before`, `bytes_lt`, `bytes_eq`) | `object_order_ok_spec`, `ObjectOrder.surj` | Accepts exactly an object order of the listing (`ObjectOrder`: one slot per record, keys `(object id, position)` strictly increasing), so every record has exactly one slot (pigeonhole) |
| `Snapshot` | `next_move_source` (over `find_object`, `move_source_from`, `names_oid`, `move_source_at`) | `next_move_source_spec` (with `find_object_spec`, `move_source_from_spec`) | Given `HEAD`'s object order: the first `HEAD` entry at or after `from` that is a `MoveSource` of entry `i` (same blob, other path, left the index), or `HEAD`'s length |
| `Snapshot` | `blob_elsewhere` (over `elsewhere_in`, `other_path_at`, `find_object`) | `blob_elsewhere_spec` (with `elsewhere_in_spec`) | For sorted listings with object orders: exactly `BlobElsewhere [index, HEAD, HEAD^1]` (two slots per listing suffice: its records of the blob are together, at distinct paths) |
| `Snapshot` | `parse_listing_attrs` | `parse_listing_attrs_spec` | Accepts exactly Git's `attrResponse` for the listing's own paths (sound and complete); flags are `Selected` of each value |
| `Snapshot` | `first_unselectable` | `first_unselectable_spec` | The first flagged entry that is not `Selectable` (regular, not reserved), or the entry count |
| `Objects` | `stored_key_state` | `stored_key_state_spec` | Exactly `storedKeySpec` (`Unlocked` only for a 119-byte file holding exactly the current config whose key authenticates it) |
| `Objects` | `parse_batch_header` (over `decimal`) | `parse_batch_header_spec`, `batchHeader_iff` | `Some size` exactly for `BatchHeader header oid size` (the requested id, ` blob `, canonical decimal of at most 19 digits, LF) |
| `Objects` | `blob_read` | `blob_read_spec` | Exactly `blobReadSpec` (read only within `maxRecord`) |
| `EndToEnd` | models over the above | `hookPlan_spec`, `hook_accepts_only_authenticated_ciphertext`, `hook_accepts_only_authenticated_ciphertext_given_history`, `hook_repairs_only_local_changes`, `stored_key_authenticates_current_config` | The pre-commit hook's end-to-end statements, with every Git/crypto/adapter contract a named hypothesis (`GitListing` A20, `GitAttributes` A19, `GitObject` A11/A21, `Realizes` A5, `HookRun` A4, `HeadAuthentic` A24); the snapshots are `Sorted` (from the parse, not assumed); see `docs/verification/V3-SECURITY-ARGUMENT.md` |
| spec (`V3Policy`) | — | `opensTo_unique`, `seal_opens`, `lock_flush_recoverable`, `objectId_plain`, `opensTo_envelopeOk`, `indexRecord_oid`, `smudgeSpec_keep_envelope`, `entryOk_indexRecord`, `localChange_held`, `localChange_unknown`, `bytesLt_irrefl`, `bytesLt_trans`, `bytesLt_total`, `Sorted.eq_of_path`, `Sorted.holds_oid`, `storedKeySpec_unlocked`, `batchHeader_unique` | Spec-level consequences used above (`indexRecord_oid`: the adapter's `entry[7..path_start-3]` is the record's object id; `Sorted.holds_oid`: in a sorted snapshot `Holds` names the one entry at the path) |

## Explicit assumptions in the statements

- **`Realizes inst prims σ`** (Protocol, Lifecycle): the `V3Primitives`
  instance computes the abstract suite's deterministic SIV with the spec's
  domain strings and AD order, preserves `&mut` slice lengths, never claims
  success wrongly, opens genuine right-sized records, and computes the
  truncated digest. Production instance `transcrypt_rs::Keyed` is checked
  by `rust/crates/transcrypt-rs/tests/v3_differential.rs` against a corpus
  from OpenSSL AES-SIV (`tests/v3/reference/differential.py`), and its
  clauses by `keyed_satisfies_the_realizes_contract` (A5).
- **`Suite`** fields: SIV output length, injectivity per AD (true of any
  deterministic AE), digest length. Unforgeability/confidentiality are
  computational assumptions (A10), not Lean theorems.
- **Lifecycle models** follow the adapter's call order (A4, reviewed in
  `V3-ASSUMPTIONS.md`).
- **Snapshot preconditions.** The snapshot queries are stated for a
  listing `parse_listing` accepted (`ListingOf`, and `Sorted` or
  `PathOrdered`); that is the only way the adapter obtains `ends`. The
  object-id lookups take an order `object_order_ok` accepted; the adapter
  sorts it and the core checks it.
- **End-to-end contracts** (`EndToEnd`): `GitListing` (A20),
  `GitAttributes` (A19), `GitObject` (A11, A21), `Realizes` (A5), the
  observed call results `HookRun` and the per-entry model `hookPlan` (A4),
  the sequencing state (A23); Git commits the checked index (A22).

## Not covered by Lean

AES-SIV/Argon2id/SHA-256 implementations and security, the Unix credential
agent's IPC and process isolation, Git's attribute/index semantics, and
filesystem atomicity. See the assumption register for evidence and residual
risk of each.
