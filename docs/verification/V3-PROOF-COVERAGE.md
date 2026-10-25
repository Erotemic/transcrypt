# Transcrypt v3: proof and test coverage ledger

**Updated 2026-10-25.** This ledger keeps a compiled proof, a functional
regression, an extraction check and a cryptographic assumption from being
reported as the same kind of evidence. See the active
[v3 roadmap](V3-ROADMAP.md), the theorem-level
[proof status](../../proofs/aeneas/v3/PROOF-STATUS.md) and the
[trust-ordered assumption register](V3-ASSUMPTIONS.md).

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
| P-02 | Git index records select the authenticated path bytes and regular-mode check | **PROVED** `parse_index_entry_spec` (exactly the spec's `IndexRecord`) | — |
| P-03 | Git objects are read only by plain object ids from one snapshot | **PROVED** `is_object_id_spec`, `objectId_plain`; **TESTED** revision-syntax and pathspec-magic filenames (`adversarial.rs`) | oid offset is spec-justified adapter slicing (A4) |
| G-06 | No plaintext reaches a remote from commits that skipped `pre-commit` | **PROVED** `record_envelope_ok_spec`, `opensTo_envelopeOk` (keyless check accepts every genuine record); **TESTED** `pre-push` refusal, keyless `audit` in a never-unlocked clone and a bare repository | Deployment of the hook or a server-side audit (A13); forged envelopes (A14) |
| P-01 | Canonical protected-path policy | **PROVED** `is_canonical_protected_path_spec` = spec `CanonicalProtectedPath` (via `List.splitOn`) | — |
| C-01 | Deterministic Argon2id + AES-SIV bytes match independent vectors | **TESTED** `tests/v3/reference/check_vectors.py`, Rust vector tests; differential corpus vs OpenSSL AES-SIV and reference Argon2id (`differential.py`, `v3_differential.rs`: 22 lengths, raw-byte paths, exhaustive tampering/truncation/extension/context changes) | External review (R-01) |
| C-02 | Config authenticated; ordered path-bound AD; no plaintext without authentication | **PROVED** `authenticate_config_spec`, `seal_record_spec`, `open_record_spec`, `open_record_complete` relative to `Realizes`; **TESTED** `keyed_satisfies_the_realizes_contract` for the production primitive | AES-SIV security (A10) |
| C-03 | Agent performs only authorized operations under the authenticated config | **PROVED** `authorize_agent_request_spec`, request framing `decode_frame_header_encode`; **TESTED** hostile-client suite | Same-UID boundary (A6) |
| G-01 | init/clone/unlock/hydrate/clean/commit/lock/re-unlock | **TESTED** `git_lifecycle.rs` | — |
| G-02 | Staged index verified (not HEAD); effective filter; no transplant | **PROVED (model)** `verifyPlan_spec`, `check_attr_paths` + **PROVED** `check_attr_response_ok_spec`; **TESTED** attribute-precedence, blob-swap, foreign-repository, truncated/extended record tests | Git semantics (A7) |
| G-03 | Crash safety of multi-file operations | **PROVED (model)** hydrate is all-or-nothing preflight and only replaces exact staged ciphertext (`hydratePlan_spec`); lock only discards recoverable plaintext (`lockEntry_spec`); **TESTED** SIGKILL fault injection at 12 points of `lock`/`hydrate`, interrupted resume, crash leftovers confined to private staging, stamp-checked replacement, operation lock | Same-UID race window between stamp check and rename (A8, A12) |
| G-04 | Derived key absent from disk while unlocked | **TESTED / DESIGN** private agent, 0600 socket in 0700 dir, stale-socket tests | Swap/core-dump hardening (A8) |
| G-05 | Lock never destroys uncommitted plaintext | **PROVED** `lock_action_spec`, **PROVED (model)** `lockEntry_spec`; **TESTED** unstaged-edit refusal | — |
| B-01 | Standalone Bash conforms to v3 | **OPEN / DEFERRED** (V7) | Bash AES-SIV dependency decision |
| R-01 | Independent algorithm, threat and adapter security review | **REVIEW (internal)** [V3-SECURITY-REVIEW.md](V3-SECURITY-REVIEW.md) | External review before security-sensitive release |

## Minimal completion gate

- [x] W-02 through W-06 each have a compiled theorem referring to the actual
      extracted Rust function, including the public slice boundary.
- [x] The invoked pure decision seam (path, config binding, seal/open,
      agent authorization, attribute check, hydrate/lock) has proofs naming
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
and the adapter's lifecycle sequencing is proved safe in a Lean model,
assuming the documented cryptographic, Git/OS and adapter contracts.* It is
**not** a claim that Transcrypt v3 is fully formally verified or that
cryptographic security is proved from first principles.
