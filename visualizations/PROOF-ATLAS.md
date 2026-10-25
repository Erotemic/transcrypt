# What exactly is formalized in Transcrypt v3?

**Source baseline:** `16cc957` (2026-10-25). This atlas explains the *tracked, compiled Lean verification reported for this snapshot*. It is not a claim that the entire Rust executable, Git, Unix or cryptographic libraries are formally verified. If the production source or generated snapshot changes, reconcile this inventory with [`PROOF-STATUS.md`](../proofs/aeneas/v3/PROOF-STATUS.md) before presenting it as current.

## Read the evidence levels literally

- **PROVED — production Rust:** a Lean `WP.spec` theorem names the **Charon/Aeneas translation of the actual `transcrypt-v3-core` Rust function** and establishes its specified output/refusal behavior. These are functional correctness proofs over the admitted inputs, not a set of test vectors. They are conditional on correct extraction (A3).
- **PROVED IF `Realizes` — production Rust:** the same source-derived theorem, but it has an explicit hypothesis that the external `V3Primitives` implementation behaves exactly like the abstract `Suite` used in the specification (A5). The RustCrypto `Keyed` implementation is tested against independent implementations; no Lean theorem discharges `Realizes` for `Keyed`.
- **PROVED — model:** Lean verifies a **separately defined sequencing model** of Git lifecycle functions, which calls the generated core functions. It does **not** prove the real Rust adapter calls the same functions on the same bytes or that native filesystem effects behave as modeled (A4).
- **TESTED/ASSUMED:** the actual Git process, Unix filesystem, credential agent, Argon2id, SHA-256, AES-SIV implementation/security and hook deployment. Real tests and review provide evidence, not end-to-end Lean proofs.

## Production functions: source-derived proof inventory

| Exact production surface | Actual proof anchors | What the theorem guarantees | Premises / gaps |
| --- | --- | --- | --- |
| `encode_config_prefix`, `encode_config`, `decode_config_exact`, `parse_config` | [`Codec.lean`](../proofs/aeneas/v3/V3Wire/Verification/Codec.lean): `encode_config_bytes`, `encode_config_refines`, `decode_config_exact_spec`, `parse_config_spec` | The config is exactly **55 bytes**, with the specified magic, arbitrary 32-byte salt and 16-byte tag. Exact field recovery, proper length/magic refusal, and round-trip behavior. | A3 translator. **Does not prove the 16-byte config authentication tag is cryptographically sound.** |
| `encode_file_header`, `decode_file_header_exact`, `parse_file_header` | [`Codec.lean`](../proofs/aeneas/v3/V3Wire/Verification/Codec.lean): `encode_file_header_refines`, `decode_file_header_exact_spec`, `parse_file_header_spec` | Every byte of the **22-byte file header**, correct config ID extraction and length/magic refusal for arbitrary inputs. | A3. **Not a proof of the AES-SIV payload.** |
| `is_protected_path`, `component_ok`, `is_canonical_protected_path` | [`Path.lean`](../proofs/aeneas/v3/V3Wire/Verification/Path.lean): `is_protected_path_spec`, `component_ok_spec`, `is_canonical_protected_path_spec` | The *current* production path validator implements the independent `CanonicalProtectedPath` specification. | A3. **At this snapshot the canonical validator excludes reserved metadata instead of enforcing `*.secret`; Git pattern evaluation is external A19, while parsed responses have source-derived proofs.** Git's path selection remains A19 / A7. |
| `bytes_eq`, `check_attr_response_ok`, `parse_index_entry`, `is_object_id` | [`Bytes.lean`](../proofs/aeneas/v3/V3Wire/Verification/Bytes.lean), [`Index.lean`](../proofs/aeneas/v3/V3Wire/Verification/Index.lean), [`Envelope.lean`](../proofs/aeneas/v3/V3Wire/Verification/Envelope.lean) | Correct byte comparison, expected `check-attr` reply, index record parsing for specified stage/mode/path, and recognition of 40/64-character lowercase-hex Git object IDs. | A3; Git commands really produce and consume the described bytes (A4/A7). |
| `parse_attr_record`, `parse_attr_response`, `is_reserved_path` | [`Attr.lean`](../proofs/aeneas/v3/V3Wire/Verification/Attr.lean): `parse_attr_response_spec`, `parse_attr_response_complete`; [`Path.lean`](../proofs/aeneas/v3/V3Wire/Verification/Path.lean): `is_reserved_path_spec` | The source-derived parser interprets the requested Git attribute response for exact raw path bytes and refuses reserved metadata. | A3; Git attribute matching and consistency are assumed A19; adapter request construction is A4. |
| `seal_action` (move/rebind gate) | [`Bytes.lean`](../proofs/aeneas/v3/V3Wire/Verification/Bytes.lean): `seal_action_spec` | Production decision for Seal, Rebind, Keep or Refuse given authenticated/source/local facts. | A3; adapter's inputs to the decision are tested/reviewed A4/A18, and crypto requires A5. |
| `decode_pkt_len`, `encode_frame_header`, `decode_frame_header` | [`Pkt.lean`](../proofs/aeneas/v3/V3Wire/Verification/Pkt.lean), [`Frame.lean`](../proofs/aeneas/v3/V3Wire/Verification/Frame.lean) | Exact admissible Git filter-protocol packet lengths, agent message header layouts and round trips. | A3; the other effectful message assembly and Unix IPC are not all translated into Lean (A4/A6). |
| `initialize_config`, `authenticate_config` | [`Protocol.lean`](../proofs/aeneas/v3/V3Wire/Verification/Protocol.lean): `initialize_config_spec`, `authenticate_config_spec` | Correct config construction, acceptance of an authentic config and specified refusal for invalid config. | **A3 + A5 `Realizes`**, A9 library correctness, A10 computational security. |
| `seal_record` | [`Protocol.lean`](../proofs/aeneas/v3/V3Wire/Verification/Protocol.lean): `seal_record_spec` | If the production function succeeds, the output bytes are **exactly** `sealedRecord` under the correct config and raw pathname and its `MaySeal` preconditions hold; errors have specified causes. | **A3 + A5.** Does not by itself prove Git invoked the filter or uploaded only encrypted objects. |
| `open_record` | [`Protocol.lean`](../proofs/aeneas/v3/V3Wire/Verification/Protocol.lean): `open_record_spec`, `open_record_complete` | If success, bytes satisfy `OpensTo` for **this config, path and record**. If authentication fails, output is zeroed and the record does not equal a genuine sealing of any same-sized plaintext. Other refusals leave the output untouched. Genuine right-sized records open correctly. | **A3 + A5.** Does not prove RustCrypto code, cryptographic hardness, credential custody or real filesystem publication. |
| `authorize_agent_request`, `record_envelope_ok` | [`Protocol.lean`](../proofs/aeneas/v3/V3Wire/Verification/Protocol.lean): `authorize_agent_request_spec`; [`Envelope.lean`](../proofs/aeneas/v3/V3Wire/Verification/Envelope.lean): `record_envelope_ok_spec` | Correct agent authorization decisions and **keyless envelope-shape validation**. | **Envelope shape is not tag authentication**; forged blobs can satisfy `EnvelopeOk` (A14). |
| `hydrate_action`, `lock_action` | [`Bytes.lean`](../proofs/aeneas/v3/V3Wire/Verification/Bytes.lean): `hydrate_action_spec`, `lock_action_spec` | Pure production decision functions return exactly the specified action. | Their filesystem application is not proved (A4/A8). |

All these theorems are statements about the generated `RustM` functions. The project's [`PROOF-STATUS.md`](../proofs/aeneas/v3/PROOF-STATUS.md) records its compiled proofs and axiom audit; translated-function correctness depends on A3. The `WP.spec` contracts also exclude panics and divergence *in the modeled computation*, for the stated inputs.

## The distinct model proof tier

The following are mathematically checked **models**, not the same source-derived proof of the Unix/Git adapter:

| Lean-defined model | Exact theorem | Proved about the model | Not proved |
| --- | --- | --- | --- |
| `hydratePlan` | [`hydratePlan_spec`](../proofs/aeneas/v3/V3Wire/Verification/Lifecycle.lean) | Proposed plaintext publication corresponds to an authenticated record under modeled input and ordering. | `git cat-file`, changes between check/use, actual `renameat` and `fsync`. |
| `lockEntry` | [`lockEntry_spec`](../proofs/aeneas/v3/V3Wire/Verification/Lifecycle.lean) | The model discards plaintext only if its encrypted form is recoverable. | Every real crash, race, hard link and background writer. |
| `verifyPlan` | [`verifyPlan_spec`](../proofs/aeneas/v3/V3Wire/Verification/Lifecycle.lean) | Modeled index verification rejects records failing the modeled checks. | Actual Git index/attribute semantics and full adapter-to-core correspondence. |
| `cleanModel`, `lockedFilterModel` | [`cleanModel_genuine`, `lockedFilterModel_spec`](../proofs/aeneas/v3/V3Wire/Verification/Filters.lean) | Modeled clean only stores genuine records under `Realizes`; locked model passes only unchanged conforming envelopes. | Real Git hooks/filters being invoked, installed and deployed. |

## Worked example: `open_record_spec`

The actual theorem starts with:

```lean
 theorem open_record_spec (h : Realizes inst prims σ)
     (config : Std.Array U8 55#usize)
     (path record out : Slice U8) :
     open_record inst prims config path record out ⦃ r => ... ⦄
```

It proves the following **for arbitrary input bytes** admitted by those types, as long as `Realizes` is supplied:

1. **`Ok`** → the returned bytes satisfy the independent predicate `OpensTo σ config path record plaintext`, so a successful release is precisely the expected authenticated opening for that config and path.
2. **`Err Authentication`** → output buffer has its original length, every output byte is zero, and the ciphertext is not an authentic sealing of any plaintext of the required size at that config and path.
3. **Other refusal branches** → output is unchanged, and the error identifies wrong size, path, configuration, envelope or config ID. No unspecified refusal branch is allowed by the theorem.

**Notice `h : Realizes ...` in the theorem statement.** This is not an invisible proof of AES-SIV. It says: *assuming the cryptographic primitive correctly produces and verifies the abstract SIV, the real Rust control flow accepts/releases and rejects/clears correctly.*

The actual production RustCrypto implementation is supported by differential vectors and mutation tests, **not** by a machine-checked `Realizes` instance. Cryptographic confidentiality and tag unforgeability are additionally A10 algorithmic assumptions. The `Aeneas` source extraction is trusted (A3). The real adapter must call `open_record` on the verified bytes and act only on its result (A4).

## Trust level of each visible operation

The Manim and SVG diagrams now share a typed operation/evidence model.
Badges are **not** inferred from the node's role color. Every green or purple
badge names a Lean theorem validated against a scene's real source file.

| Operation on screen | Evidence category | Precise basis |
| --- | --- | --- |
| Git path selection | Trusted platform | A19 (Git attribute semantics); parser is separately source-proved |
| `parse_attr_response` | Source-derived proof | `parse_attr_response_spec` |
| Argon2id key derivation | Trusted cryptographic library | A9/A10; reference/differential tests |
| `authenticate_config` | Conditional source-derived proof | `authenticate_config_spec` if `Realizes` A5 |
| Local stored key / optional agent | Tested adapter | A17 / A6, OS custody and same-UID risks |
| Git clean filter and index storage | Tested adapter plus trusted Git | A4 / A7, not whole-program proof |
| `seal_record` and `open_record` | Conditional source-derived proofs | `seal_record_spec`, `open_record_spec`, both if `Realizes` |
| RustCrypto AES-SIV | Trusted cryptographic library | A5/A9/A10; not Lean proved |
| Record header encoder | Source-derived proof | `encode_file_header_refines` |
| Rename action decision | Source-derived proof | `seal_action_spec`; actual rebind A4/A18 tested |
| Keyless envelope validator | Source-derived proof of **shape only** | `record_envelope_ok_spec`; does not check tag A14 |
| History audit / pre-push / remote hooks | Tested adapter + external deployment | A4/A13; optional keyed auth separate |
| Pure lock gate | Source-derived proof | `lock_action_spec` |
| Hydrate/lock/verify sequencing | Model proof | `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` |
| Actual native worktree writer and key deletion | Tested adapter/OS | A4/A8/A17, not Lean proved |
| Charon/Aeneas source translation | Trusted premise | A3; pinned and reproduced, not itself a proof |

The moving tokens are for **data provenance**, not for evidence. Their kinds
(plaintext, ciphertext record, key, raw path, metadata, decision) remain
separate from these theorem/test/assumption classifications. A decision token
is not a claim that an OS write has already happened.

## The big security claim we cannot yet assert as a Lean theorem

> "For every file the user selected, no possible normal Git operation can publish that file's plaintext to a public history."

That is **not** a proved end-to-end property today. Such a theorem would need correspondence for Git attribute selection, clean-filter invocation, adapter input/output, index operations, and remote policy, not just the verified core. Git and OS semantics are assumed; adapter conformance is structurally narrowed, reviewed and adversarially tested.

The theorem-backed claim is narrower but valuable: **the actual Rust v3 protocol core has the specified byte-level and authentication-decision behavior, under an explicit primitive contract, and the sequencing models satisfy their own stated invariants.**

For the authoritative detail, use [`V3-PROOF-COVERAGE.md`](../docs/verification/V3-PROOF-COVERAGE.md), [`V3-ASSUMPTIONS.md`](../docs/verification/V3-ASSUMPTIONS.md) and [`PROOF-STATUS.md`](../proofs/aeneas/v3/PROOF-STATUS.md). Product-design decisions are separate: in this snapshot generic Git-attribute selection, local stored-key unlock (default), authenticated rename rebinding and explicit v2 migration are implemented and tested. Their effectful adapters are not end-to-end source-derived proved.
