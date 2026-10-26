# V3 traceability and refinement targets

This correspondence table refers to the independent
[`V3-AUTHENTICATED-P0.md`](../specs/V3-AUTHENTICATED-P0.md). Rust code
must be changed to comply with that contract, not vice versa.

| Protocol clause | Production Rust | Independent conformance evidence | Lean theorem (proved) |
|---|---|---|---|
| Config bytes 0..54, magic, salt, verifier | `transcrypt-v3-core::{encode_config_prefix,encode_config,decode_config_exact,parse_config}` | core unit tests, `vectors.tsv` | `encode_config_refines`, `decode_config_exact_spec`, `parse_config_spec`, `parse_config_encode_config` |
| File header bytes 0..21, minimum 38 | `transcrypt-v3-core::{encode_file_header,decode_file_header_exact,parse_file_header}` | core unit tests, Rust negative tests | `encode_file_header_refines`, `decode_file_header_exact_spec`, `parse_file_header_spec` |
| Argon2id v19 fixed params/64B key | `transcrypt-v3::derive_key` | Python argon2-cffi vector | External assumption (A9/A10) |
| Canonical path policy (suffix-free; reserved metadata refused) | `transcrypt-v3-core::{is_reserved_path,is_canonical_protected_path}` | Rust path tests, raw `%f` Git test, arbitrary-pattern workflow test | `is_canonical_protected_path_spec`, `is_reserved_path_spec` |
| Deterministic, path-bound AES-SIV sealing | `transcrypt-v3-core::seal_record` via `Keyed` | OpenSSL-backed vectors, `keyed_satisfies_the_realizes_contract` | `seal_record_spec` (relative to `Realizes`) |
| Metadata binding and fail closed | `transcrypt-v3-core::{authenticate_config,open_record}` | tampering, wrong password, cross-path and foreign-record tests | `authenticate_config_spec`, `open_record_spec`, `open_record_complete` |
| Credential authorization | `transcrypt-v3-core::authorize_agent_request`, `session::{start,serve,transaction}` | hostile-client and stale-socket tests | `authorize_agent_request_spec` |
| Protected-file selection and staged tree safety | `transcrypt-v3-core::parse_attr_record`, `parse_attr_response`, `parse_listing_attrs`, `first_unselectable`, `git::{protected_flags,listing_flags}`, `lifecycle::check_index`, pre-commit hook | nested attributes, forged object, blob-swap, hostile-move tests | `parse_attr_record_spec`, `parse_attr_response_spec`, `parse_attr_response_complete`, `parse_listing_attrs_spec`, `first_unselectable_spec`, `verifyPlan_spec` |
| Git snapshots (index and tree listings) | `transcrypt-v3-core::{parse_listing,listing_fields}`, `git::Listing` | listing fuzzing, raw/TAB/newline path tests | `parse_listing_spec`, `listing_fields_spec` |
| Pre-commit repair inputs (local changes, move sources) | `transcrypt-v3-core::{held_entries,is_local_change,next_move_source}`, `lifecycle::{seal_snapshot,open_moved}` | rename, hostile-move, merge/cherry-pick/rebase tests | `held_entries_spec`, `is_local_change_spec`, `next_move_source_spec`, `hook_repairs_only_local_changes` |
| Hook check of settled and moved records | `transcrypt-v3-core::{held_entries,blob_elsewhere}`, `lifecycle::check_staged` | locked-rename, `--amend`, unbound-move tests | `held_entries_spec`, `blob_elsewhere_spec`, `hookPlan_spec`, `hook_accepts_only_authenticated_ciphertext` |
| Stored-key unlock | `transcrypt-v3-core::stored_key_state`, `credential::{lookup,stored_lookup}` | legacy, damaged, stale-after-rekey tests | `stored_key_state_spec`, `stored_key_authenticates_current_config` |
| Git object replies | `transcrypt-v3-core::{parse_batch_header,blob_read}`, `git::Objects::blob` | reply fuzzing, oversized-blob tests | `parse_batch_header_spec`, `blob_read_spec` |
| Smudge decision | `transcrypt-v3-core::smudge_action`, `main::Filters::convert` | stale-key, old-history, tamper tests | `smudge_action_spec`, `smudgeModel_spec` |
| Clone hydration | `transcrypt-v3-core::hydrate_action`, `main::hydrate` | clone, staged-only index, preflight, interruption, crash-leftover tests | `hydrate_action_spec`, `hydratePlan_spec` |
| Lock | `transcrypt-v3-core::lock_action`, `main::lock`, `session::stop` | unstaged-edit refusal, interrupted-lock resume | `lock_action_spec`, `lockEntry_spec` |

## Trusted computation boundaries

The future Aeneas formalization must translate `transcrypt-v3-core` **as
shipped**; the separate `V3Wire.lean` file only models the intended wire
shape. The RustCrypto `aes-siv` and `argon2` implementations remain opaque
cryptographic dependencies until separately reviewed or proved. Git, OS
paths/permissions, randomness, process execution, persistence, and the
Unix-domain credential agent and its in-memory key remain external to the pure wire proof.

A proof of the Rust pure core **does not prove** password hardness,
cryptographic authenticity, endpoint secrecy, Bash compliance, or safe Git
transactions. Each requires separate review/proofs. The first core theorem
should be `parse_config(encode_config(fields)) = Ok(fields)` for all byte
arrays of the exact declared sizes, followed by the corresponding file
header roundtrip and rejection of wrong magic/truncation. Bind every
statement to the generated Aeneas function and source revision.

## Bash correspondence (future)

The existing Bash implementation does not implement this protocol. A
conforming Bash v3 can share the same `.transcrypt/config`, 22-byte file
header, ordered two-element SIV associated data, strict errors, and fixed
Argon2id parameters **only if** its permitted dependencies can provide
those operations without emitting key material in process arguments. If not,
do not claim interoperability or silently weaken the protocol; escalate to
the maintainer's dependency-policy decision. Hand review must cite the
actual Bash functions and independently run the shared vectors.

## Operational evidence added after P0

The actual adapter uses an in-memory credential process with a Unix-domain
socket, rather than persisting `SecretKey` in `.git`. Its IPC schema is
specified in `V3-AUTHENTICATED-P0.md` separately from committed ciphertext
bytes. The Git integration tests exercise init, wrong-password unlock, socket
permissions, staged-index hydration, rejection of a divergent second file
without changing the first, repeatable hydration, failure-to-lock on untracked
secrets, agent termination and re-unlock. The Unix/IPC implementation has no Charon
or Aeneas refinement claim; only the pure v3 core is targeted for extraction.

## Fixed-width production decoder boundary

As of this implementation increment, the actual `transcrypt-v3-core`
parsers call these fixed-array content decoders after length checking:

| Public API (called by crypto adapter) | Production content decision | Independent Lean contract |
|---|---|---|
| `parse_config(&[u8])` | `decode_config_exact(&[u8; 55])` | `V3Wire.decodeConfigShape` |
| `parse_file_header(&[u8])` | `decode_file_header_exact(&[u8; 22])` | `V3Wire.decodeFileHeaderShape`, with the public ≥38-byte precondition |
| `encode_config(&Config)` | Production fixed array encoder | `V3Wire.encodeConfig` |
| `encode_file_header(&[u8; 16])` | Production fixed array encoder | First 22 bytes of `V3Wire.encodeFile` |

This is source-level factoring, **not yet an Aeneas-to-Lean refinement
proof**. The proof must tie generated functions to these independent
contracts while handling `Result`, fixed-width `U8` arrays, conversion of
bytes to list elements, and bounds checks. AES-SIV authentication and
Argon2id are independent external assumptions; successful header parsing
must never be treated as authentication.

## Aeneas refinement bridge and concrete proof targets

`proofs/aeneas/prepare-v3-refinement.sh` imports production Aeneas output and
the independently maintained `Transcrypt.V3WireCodec` into the same Lake
project. This is a shared elaboration boundary, not a proof of equivalence.
All proof inputs can be exported with `export_v3_proof_inputs.py` after an
actual extraction. Proof theorems must use the generated Lean functions, not
handwritten stand-ins, and establish at least:

1. `encode_config` yields the 7-byte magic, 32-byte salt, and 16-byte tag
   exactly as the independent `encodeConfig` specifies.
2. `decode_config_exact` succeeds exactly when the fixed 55-byte header has
   the correct 7-byte prefix, returns the original salt/tag, and rejects all
   incorrect prefix bytes.
3. `encode_file_header` produces the exact 6-byte version marker followed by
   the 16-byte public configuration identifier.
4. `decode_file_header_exact` accepts precisely the correct 22-byte versioned
   header, returns its identifier, and rejects wrong magic/version bytes.
5. The slice-based production public parsers correctly enforce the additional
   full-length/truncation requirements. These are **not** covered merely by
   proving the four fixed-width codecs.

Crypto correctness (Argon2id/AES-SIV external dependency) and end-to-end
Git/OS state transitions remain distinct refinement/security obligations.

## Reviewed, version-controlled production extraction

The production Rust codec's generated semantics live at
`proofs/aeneas/v3/V3Wire/Extraction/Funs.lean` and
`proofs/aeneas/v3/V3Wire/Extraction/Types.lean`, along with explicitly
tracked external assumptions, toolchain pins, and `SNAPSHOT.json` source
hashes. The code is Aeneas-generated from the production crate, not an
alternative manually authored Rust model.

As of 2026-10-25 the verification modules under `V3Wire/Verification/`
prove the full extracted encoder/decoder loops, errors and length checks, and
every protocol decision of the core, relative to the explicit primitive
contract `Realizes` (see the table above and `PROOF-STATUS.md`). The
cryptographic primitives themselves remain external assumptions. The
snapshot-integrity test alone is still not verification.

## Experimental v3 pathname binding (no wire-core changes)

The actual v3 adapter authenticates the canonical raw Git-relative path of
every attribute-selected file as AES-SIV AD component 3. Git's `%f` provides the
argument to clean/smudge; staged index names are the authoritative input for
verify-index, hydrate and lock. The credential-agent IPC transports the same
raw bytes. The independent Python vector fixture tests the 3-element AD
against OpenSSL-backed AES-SIV; Rust integration tests reject swapping two
valid staged encrypted Git blobs. The fixed 55-byte metadata and 22-byte file
headers, and the Aeneas-tracked pure wire codec, are byte-for-byte unchanged.

This is a *cryptographic profile incompatibility* with the earlier v3 P0
prototype. Old ciphertext must be exported before upgrading/reinitializing.
No unproven fallback or multi-version complexity was added. The path policy
and the AD-carrying seal/open control flow are now proved in the core; the
AES-SIV implementation remains an external assumption (A5/A9).
