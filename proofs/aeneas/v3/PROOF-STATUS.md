# Formal verification ledger — production v3 core

**Reconciled 2026-10-25.** Every theorem below is about the Charon/Aeneas
translation of the production `rust/crates/transcrypt-v3-core/src/lib.rs`
(pinned by `SNAPSHOT.json`), stated against the independent specification in
`proofs/lean/Transcrypt/{V3Wire,V3WireCodec,V3Policy}.lean`. All are `WP.spec`
triples, so they also exclude panics (index, overflow) and divergence. The
default `V3Wire` target builds all of them;
`bash proofs/aeneas/check-v3-axioms.sh` confirms the 31 headline theorems use
only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`,
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
| `Codec` | `decode_config_exact`, `decode_file_header_exact` | `decode_{config,file_header}_exact_spec` | `Ok` iff magic matches, with exact fields; `Err Magic` iff magic differs; never `Err Length` |
| `Codec` | `parse_config`, `parse_file_header` (public slice boundary) | `parse_config_spec`, `parse_file_header_spec` | Exactly the spec's `decodeConfigShape` / `decodeFileHeaderShape`, with `Length` vs `Magic` classified |
| `Codec` | roundtrips | `decode_config_exact_encode_config`, `decode_file_header_exact_encode_file_header`, `parse_config_encode_config` | Decoding an encoding returns the input |
| `Bytes` | `bytes_eq`, `filter_suffix_at`, `check_attr_response_ok` | `bytes_eq_spec`, `filter_suffix_at_spec`, `check_attr_response_ok_spec` | Equality decision; Git `check-attr` response accepted iff it equals `expectedAttrResponse request` |
| `Bytes` | `hydrate_action`, `lock_action` | `hydrate_action_spec`, `lock_action_spec` | Exactly `hydrateSpec` / `lockSpec` |
| `Path` | `is_protected_path`, `component_ok`, `is_canonical_protected_path` | `is_protected_path_spec`, `component_ok_spec`, `is_canonical_protected_path_spec` | Exactly the spec's `Protected` / `CanonicalProtectedPath` (defined with `List.splitOn`) |
| `Index` | `parse_index_entry` | `parse_index_entry_spec` | Accepts exactly the spec's `IndexRecord` (stage 0, path after the first TAB, `100644` flag) and returns that path |
| `Frame` | `encode_be_u32`, `decode_be_u32`, `encode_frame_header`, `decode_frame_header` | `encode_be_u32_spec`, `decode_be_u32_spec`, `encode_frame_header_spec`, `decode_frame_header_spec`, `decode_frame_header_encode` | Agent request header is exactly the spec's `frameHeader`; decoding inverts encoding |
| `Envelope` | `is_object_id`, `record_envelope_ok` | `is_object_id_spec`, `record_envelope_ok_spec` | Object ids passed to Git are exactly the spec's `ObjectId` (40/64 lowercase hex: never revision syntax or an option, `objectId_plain`); the keyless check is exactly `EnvelopeOk` (size bound, magic, config id), which every genuine record satisfies (`opensTo_envelopeOk`) |
| `Protocol` | `initialize_config` | `initialize_config_spec` | Output is the spec layout and authenticates |
| `Protocol` | `authenticate_config` | `authenticate_config_spec` | `Ok` iff `ConfigAuthentic`; refusals classified |
| `Protocol` | `seal_record` | `seal_record_spec` | `Ok` ⇒ `MaySeal` and output = `sealedRecord`; every refusal names a violated precondition or primitive failure |
| `Protocol` | `open_record` | `open_record_spec`, `open_record_complete` | `Ok` ⇒ `OpensTo` for exactly the released bytes; authentication failure ⇒ zeroed buffer and no genuine record exists; other refusals leave the buffer untouched; genuine right-sized records always open to their plaintext |
| `Protocol` | `authorize_agent_request` | `authorize_agent_request_spec` | Exactly `authorizeSpec` |
| `Lifecycle` | adapter sequencing models over the above | `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec`, `check_attr_paths` | Hydrate only replaces exact staged ciphertext by its authentic plaintext (all-or-nothing); lock only discards plaintext the record restores; verify-index success ⇒ every staged record opens at its own path; accepted check-attr ⇒ filter reported for every path |
| spec (`V3Policy`) | — | `opensTo_unique`, `seal_opens`, `lock_flush_recoverable`, `expectedAttrResponse_paths`, `objectId_plain`, `opensTo_envelopeOk`, `indexRecord_oid` | Spec-level consequences used above (`indexRecord_oid`: the adapter's `entry[7..path_start-3]` is the record's object id) |

## Explicit assumptions in the statements

- **`Realizes inst prims σ`** (Protocol, Lifecycle): the `V3Primitives`
  instance computes the abstract suite's deterministic SIV with the spec's
  domain strings and AD order, preserves `&mut` slice lengths, never claims
  success wrongly, opens genuine right-sized records, and computes the
  truncated digest. Production instance `transcrypt_v3::Keyed` is checked by
  independent vectors and `keyed_satisfies_the_realizes_contract` (A5).
- **`Suite`** fields: SIV output length, injectivity per AD (true of any
  deterministic AE), digest length. Unforgeability/confidentiality are
  computational assumptions (A10), not Lean theorems.
- **Lifecycle models** follow the adapter's call order (A4, reviewed in
  `V3-ASSUMPTIONS.md`).

## Not covered by Lean

AES-SIV/Argon2id/SHA-256 implementations and security, the Unix credential
agent's IPC and process isolation, Git's attribute/index semantics, and
filesystem atomicity. See the assumption register for evidence and residual
risk of each.
