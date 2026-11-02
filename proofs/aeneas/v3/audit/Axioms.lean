import V3Wire

/-! Axiom audit for the theorems listed in `PROOF-STATUS.md`, in ledger
    order. Not part of the normal build: run
    `bash proofs/aeneas/check-v3-axioms.sh`, which fails unless every
    theorem depends only on Lean's standard axioms. -/

open Transcrypt.V3Verification

-- Refinement
#print axioms extracted_config_magic_matches_spec
#print axioms extracted_file_magic_matches_spec
#print axioms extracted_magic_disjoint
-- Codec
#print axioms encode_config_prefix_bytes
#print axioms encode_config_bytes
#print axioms encode_file_header_bytes
#print axioms encode_config_refines
#print axioms encode_file_header_refines
-- Codec
#print axioms decode_config_exact_spec
#print axioms decode_file_header_exact_spec
-- Codec
#print axioms parse_config_spec
#print axioms parse_file_header_spec
-- Codec
#print axioms decode_config_exact_encode_config
#print axioms decode_file_header_exact_encode_file_header
#print axioms parse_config_encode_config
-- Bytes
#print axioms bytes_eq_spec
#print axioms matches_at_spec
#print axioms find_byte_spec
-- Bytes
#print axioms hydrate_action_spec
#print axioms lock_action_spec
-- Path
#print axioms ends_with_spec
#print axioms is_attributes_path_spec
#print axioms is_reserved_path_spec
#print axioms is_policy_path_spec
#print axioms component_ok_spec
#print axioms is_canonical_protected_path_spec
-- Attr
#print axioms parse_attr_record_spec
#print axioms parse_attr_response_spec
#print axioms parse_attr_response_complete
-- Index
#print axioms parse_index_entry_spec
-- Frame
#print axioms encode_be_u32_spec
#print axioms decode_be_u32_spec
#print axioms encode_frame_header_spec
#print axioms decode_frame_header_spec
#print axioms decode_frame_header_encode
-- Bytes (repair)
#print axioms needs_record_spec
#print axioms repair_plan_spec
#print axioms repairPlanSpecOf_injective
#print axioms repair_plan_repairs_only_local
#print axioms needs_record_skip
#print axioms Transcrypt.V3Policy.repairSpec_seal
#print axioms Transcrypt.V3Policy.repairSpec_rebind
#print axioms Transcrypt.V3Policy.repairSpec_keep
#print axioms Transcrypt.V3Policy.repairSpec_repairs_only_local
#print axioms Transcrypt.V3Policy.repairSpec_unread
#print axioms entry_check_spec
-- Envelope
#print axioms is_object_id_spec
#print axioms record_envelope_ok_spec
#print axioms record_envelope_prefix_ok_spec
#print axioms record_envelope_prefix_ok_record
#print axioms smudge_action_spec
-- Pkt
#print axioms decode_pkt_len_spec
-- Protocol
#print axioms initialize_config_spec
-- Protocol
#print axioms authenticate_config_spec
-- Protocol
#print axioms seal_record_spec
-- Protocol
#print axioms open_record_spec
#print axioms open_record_complete
-- Protocol
#print axioms authorize_agent_request_spec
-- Lifecycle
#print axioms hydratePlan_spec
#print axioms lockEntry_spec
#print axioms verifyPlan_spec
-- Filters
#print axioms cleanModel_spec
#print axioms cleanModel_genuine
#print axioms cleanModel_idempotent
#print axioms lockedFilterModel_spec
#print axioms smudgeModel_spec
-- SnapshotOrder
#print axioms bytes_lt_spec
#print axioms listing_ordered_spec
-- SnapshotOrder
#print axioms parse_listing_spec
-- SnapshotListing
#print axioms listing_fields_spec
#print axioms FieldsOf.slices
-- SnapshotLookup
#print axioms find_entry_spec
#print axioms find_path_spec
#print axioms record_is_spec
-- SnapshotLookup
#print axioms held_entries_spec
-- SnapshotLookup
#print axioms provenance_of_spec
#print axioms entry_provenance_spec
-- SnapshotMoves
#print axioms object_order_ok_spec
#print axioms ObjectOrder.surj
-- SnapshotMoves
#print axioms next_move_source_spec
#print axioms find_object_spec
#print axioms move_source_from_spec
-- SnapshotMoves
#print axioms blob_elsewhere_spec
#print axioms elsewhere_in_spec
-- SnapshotAttrs
#print axioms parse_listing_attrs_spec
-- SnapshotAttrs
#print axioms first_unselectable_spec
-- SnapshotPolicy
#print axioms policy_unchanged_spec
#print axioms same_policy_spec
#print axioms policy_unchanged_sound
#print axioms Transcrypt.V3Policy.PolicyUnchanged.agree
#print axioms Transcrypt.V3Policy.PolicyUnchanged.holds
#print axioms Transcrypt.V3Policy.PolicyPath.reserved
-- Objects
#print axioms stored_key_state_spec
-- Objects
#print axioms parse_batch_header_spec
#print axioms batchHeader_iff
-- Objects
#print axioms blob_read_spec
-- EndToEnd
#print axioms hookPlan_spec
#print axioms hook_accepts_only_authenticated_ciphertext
#print axioms hook_accepts_only_authenticated_ciphertext_given_history
#print axioms hook_provenance
#print axioms hook_skips_only_unrepairable
#print axioms hook_repairs_only_local_changes
#print axioms stored_key_authenticates_current_config
#print axioms hook_policy_guard
#print axioms hook_settled_policy_unchanged
-- ProductSecurity
#print axioms hook_full_check_authenticates
#print axioms pre_commit_check_modes
#print axioms keyed_publication_authenticates
#print axioms head_authentic_of_checked_commit
#print axioms keyed_history_stays_authenticated
#print axioms unguarded_check_is_full
#print axioms policy_unchanged_of_guard
#print axioms keyed_check_authenticates_given_guard
#print axioms keyed_history_authenticated_by_guard
#print axioms checkout_releases_only_authenticated_plaintext
#print axioms checkout_opens_genuine_records
#print axioms repair_never_launders
#print axioms stored_key_binds_file_operations
-- spec (V3Policy)
#print axioms Transcrypt.V3Policy.opensTo_unique
#print axioms Transcrypt.V3Policy.seal_opens
#print axioms Transcrypt.V3Policy.lock_flush_recoverable
#print axioms Transcrypt.V3Policy.objectId_plain
#print axioms Transcrypt.V3Policy.opensTo_envelopeOk
#print axioms Transcrypt.V3Policy.indexRecord_oid
#print axioms Transcrypt.V3Policy.smudgeSpec_keep_envelope
#print axioms Transcrypt.V3Policy.entryOk_indexRecord
#print axioms Transcrypt.V3Policy.localChange_held
#print axioms Transcrypt.V3Policy.localChange_unknown
#print axioms Transcrypt.V3Policy.provenanceIs_unique
#print axioms Transcrypt.V3Policy.provenanceIs_held
#print axioms Transcrypt.V3Policy.localChange_iff_provenance
#print axioms Transcrypt.V3Policy.bytesLt_irrefl
#print axioms Transcrypt.V3Policy.bytesLt_trans
#print axioms Transcrypt.V3Policy.bytesLt_total
#print axioms Transcrypt.V3Policy.Sorted.eq_of_path
#print axioms Transcrypt.V3Policy.Sorted.holds_oid
#print axioms Transcrypt.V3Policy.storedKeySpec_unlocked
#print axioms Transcrypt.V3Policy.batchHeader_unique
