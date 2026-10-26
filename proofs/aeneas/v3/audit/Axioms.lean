import V3Wire

/-! Axiom audit for the headline v3 theorems. Not part of the normal build:
    run `bash proofs/aeneas/check-v3-axioms.sh`, which fails unless every
    theorem depends only on Lean's standard axioms. -/

open Transcrypt.V3Verification

#print axioms encode_config_refines
#print axioms encode_file_header_refines
#print axioms parse_config_spec
#print axioms parse_file_header_spec
#print axioms decode_config_exact_spec
#print axioms decode_file_header_exact_spec
#print axioms parse_config_encode_config
#print axioms is_reserved_path_spec
#print axioms is_canonical_protected_path_spec
#print axioms parse_attr_record_spec
#print axioms parse_attr_response_spec
#print axioms parse_attr_response_complete
#print axioms hydrate_action_spec
#print axioms lock_action_spec
#print axioms initialize_config_spec
#print axioms authenticate_config_spec
#print axioms seal_record_spec
#print axioms open_record_spec
#print axioms open_record_complete
#print axioms authorize_agent_request_spec
#print axioms hydratePlan_spec
#print axioms lockEntry_spec
#print axioms verifyPlan_spec
#print axioms Transcrypt.V3Policy.opensTo_unique
#print axioms Transcrypt.V3Policy.lock_flush_recoverable
#print axioms parse_index_entry_spec
#print axioms encode_frame_header_spec
#print axioms decode_frame_header_spec
#print axioms decode_frame_header_encode
#print axioms is_object_id_spec
#print axioms record_envelope_ok_spec
#print axioms Transcrypt.V3Policy.opensTo_envelopeOk
#print axioms Transcrypt.V3Policy.indexRecord_oid
#print axioms cleanModel_spec
#print axioms cleanModel_genuine
#print axioms cleanModel_idempotent
#print axioms lockedFilterModel_spec
#print axioms smudge_action_spec
#print axioms smudgeModel_spec
#print axioms Transcrypt.V3Policy.smudgeSpec_keep_envelope
#print axioms seal_action_spec
#print axioms Transcrypt.V3Policy.sealSpec_repairs_only_local
#print axioms decode_pkt_len_spec
