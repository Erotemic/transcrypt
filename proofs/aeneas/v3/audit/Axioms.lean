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
#print axioms is_reserved_path_spec
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
#print axioms seal_action_spec
#print axioms Transcrypt.V3Policy.sealSpec_repairs_only_local
#print axioms Transcrypt.V3Policy.sealSpec_seal_plain
#print axioms Transcrypt.V3Policy.sealSpec_rebind_moved
-- Envelope
#print axioms is_object_id_spec
#print axioms record_envelope_ok_spec
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
-- Snapshot
#print axioms bytes_lt_spec
#print axioms listing_ordered_spec
-- Snapshot
#print axioms parse_listing_spec
-- Snapshot
#print axioms listing_fields_spec
#print axioms FieldsOf.slices
-- Snapshot
#print axioms find_entry_spec
#print axioms find_path_spec
#print axioms record_is_spec
-- Snapshot
#print axioms held_entries_spec
-- Snapshot
#print axioms is_local_change_spec
-- Snapshot
#print axioms object_order_ok_spec
#print axioms ObjectOrder.surj
-- Snapshot
#print axioms next_move_source_spec
#print axioms find_object_spec
#print axioms move_source_from_spec
-- Snapshot
#print axioms blob_elsewhere_spec
#print axioms elsewhere_in_spec
-- Snapshot
#print axioms parse_listing_attrs_spec
-- Snapshot
#print axioms first_unselectable_spec
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
#print axioms hook_repairs_only_local_changes
#print axioms stored_key_authenticates_current_config
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
#print axioms Transcrypt.V3Policy.bytesLt_irrefl
#print axioms Transcrypt.V3Policy.bytesLt_trans
#print axioms Transcrypt.V3Policy.bytesLt_total
#print axioms Transcrypt.V3Policy.Sorted.eq_of_path
#print axioms Transcrypt.V3Policy.Sorted.holds_oid
#print axioms Transcrypt.V3Policy.storedKeySpec_unlocked
#print axioms Transcrypt.V3Policy.batchHeader_unique
