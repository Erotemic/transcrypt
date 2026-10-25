# Transcrypt v3: trust-ordered assumption register

**Created 2026-10-25.** Every guarantee about the Rust v3 implementation is
conditional on the assumptions below. They are ordered from **least trusted**
(our own newest code, most likely to be wrong) to **most trusted** (standard
cryptographic hardness). Work discharges them in that order: an assumption is
only worth attacking after everything less trusted than it has been
discharged or explicitly bounded.

Status vocabulary matches [V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md):
**PROVED** (Lean theorem about the Aeneas translation of the production
Rust), **TESTED** (real Rust/Git tests or independent vectors), **REVIEWED**
(argued in a document), **ASSUMED** (stated and bounded, not discharged).

| # | Assumption (least → most trusted) | What relies on it | Status and evidence | Residual |
|---|---|---|---|---|
| A1 | The pure protocol core decides correctly: path policy, config authentication gate, seal/open gates and their order, envelope/config binding, double-encryption refusal, size bounds, output zeroing, hydrate/lock actions, agent authorization, Git `check-attr` verdict | Every security property | **Discharged — PROVED**, see [below](#discharged-by-proof) | None beyond A3, given A5 |
| A2 | The wire codec (55-byte config, 22-byte header, slice-length gates) matches the spec | Interop, envelope parsing | **Discharged — PROVED** (full-field, every outcome, roundtrips) | None beyond A3 |
| A3 | Charon/Aeneas/hax translation is faithful and Lean's kernel is sound | Meaning of A1/A2 proofs | ASSUMED; pinned toolchain, CI re-extraction gate, Rust unit tests exercise the same functions; axiom audit shows only Lean's standard axioms | Translator bugs; mitigated by tests of the same source |
| A4 | The adapter calls the core on the right inputs and acts only on `Ok` results: exact Git `%f`/index path bytes, on-disk config bytes, staged record bytes; no plaintext path bypasses `open_record`; its multi-file loops follow the Lean lifecycle models | Connecting A1 to real effects | **Bounded**: lifecycle sequencing PROVED in Lean models (`hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec`); call sites REVIEWED (table below); TESTED (Git lifecycle and adversarial suites) | Adapter Rust itself is not proved |
| A5 | `Keyed` realizes the `V3Primitives` contract (`Realizes` in Lean): AES-SIV with the exact domain strings and AD order, SHA-256 truncation, output lengths | Turning A1 into authenticity statements | TESTED: independent OpenSSL/argon2-cffi vectors byte-identical to Rust; RustCrypto known-answer tests | RustCrypto implementation (A9) |
| A6 | The credential agent relays core results faithfully: same binary, framed IPC, 0600 socket in 0700 directory, key only via startup pipe | Lock/hydrate decisions computed across the process boundary | TESTED (hostile-client tests, stale-socket tests) | Same-UID processes are inside the trust boundary |
| A7 | Git semantics: `%f` passes exact path bytes; `ls-files --stage -z` and `check-attr --cached -z` formats; `filter.required=true` enforcement; index vs HEAD; hooks are local only | Which bytes are authenticated and which files are protected | TESTED with real Git (raw paths, attribute precedence, index/HEAD divergence) | Git versions not tested; server-side policy out of scope |
| A8 | OS/filesystem: rename atomicity within a filesystem, fsync durability, permission enforcement, no concurrent hostile same-UID changes to file *contents* | Crash safety, no plaintext outside protected paths | **Narrowed**: fd-relative `openat`/`renameat` resolution (parent swaps cannot redirect writes), private 0700 staging, non-dumpable agent; TESTED (race, crash-leftover, symlink, interrupted lock/hydrate, dumpability) | Same-UID content races; root; hibernation |
| A9 | RustCrypto `aes-siv 0.8.0`, `argon2 0.6.0`, `sha2 0.10.9` are correct implementations | A5 | TESTED by independent vectors; crates pinned with `=` | `aes-siv` has had no independent audit |
| A10 | AES-SIV is a secure deterministic AEAD (RFC 5297), Argon2id resists offline guessing at m=64 MiB/t=3/p=1, SHA-256 truncation is collision resistant enough to act as a public discriminator | Confidentiality/unforgeability meaning of everything above | ASSUMED: standard assumptions | Deterministic encryption leaks equality per path; rollback of Git history not prevented |

## Discharged by proof

All theorems below are about the Aeneas translation of the production core
and compile without `sorry`; `check-v3-axioms.sh` shows only Lean's standard
axioms. Statement details: [PROOF-STATUS](../../proofs/aeneas/v3/PROOF-STATUS.md).

| Assumption (as previously trusted) | Theorem(s) |
| --- | --- |
| Encoders write the spec layout | `encode_config_bytes`, `encode_config_refines`, `encode_file_header_bytes`, `encode_file_header_refines` |
| Decoders and public parsers implement the spec grammar | `decode_*_exact_spec`, `parse_config_spec`, `parse_file_header_spec`, roundtrips |
| Path canonicalization policy | `is_canonical_protected_path_spec` (equals spec `CanonicalProtectedPath`) |
| Config authentication | `authenticate_config_spec`, `initialize_config_spec` |
| Clean never emits anything but a correct record, never double-encrypts | `seal_record_spec` |
| Smudge/verify release only authentic plaintext for this config and path; failure leaks nothing | `open_record_spec`, `open_record_complete`, `opensTo_unique` |
| Agent authorization and framing | `authorize_agent_request_spec`, `decode_frame_header_encode` |
| Effective filter attribute check | `check_attr_response_ok_spec`, `check_attr_paths` |
| Index record parsing | `parse_index_entry_spec` |
| Hydrate/lock never lose data; verify-index soundness | `hydrate_action_spec`, `lock_action_spec`, `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` |

## Adapter call-site review (A4)

Each effect in `rust/crates/transcrypt-v3/src/{main,session,lib}.rs` and the
verified decision that gates it:

| Adapter action | Gate (verified core function) | Inputs passed | Acts only on |
| --- | --- | --- | --- |
| `clean` filter output | agent `Encrypt` → `seal_record` | config bytes read from `.transcrypt/config`; Git `%f` bytes (argv, raw); stdin | `Ok` (else the filter fails and Git aborts) |
| `smudge` filter output | agent `Decrypt` → `open_record` | same config; Git `%f`; staged blob from stdin | `Ok` |
| Agent request framing (client and server) | `encode_frame_header` / `decode_frame_header`, `encode_be_u32` / `decode_be_u32` | opcode, config, path and body lengths | proved roundtrip |
| Agent request dispatch | `authorize_agent_request` before reading the body | opcode, supplied config, config authenticated at startup, path, length | `Ok(op)` |
| Agent startup | `authenticate_config` | config bytes and the piped key | `Ok` |
| `unlock` / `init` | `authenticate_config` / `initialize_config` (via `Keyed`) | config bytes / fresh salt | `Ok`, before any persistent effect |
| `verify-index` | `check_attr_response_ok`, then agent `Decrypt` per entry | exact request bytes sent to `check-attr`; NUL-delimited index paths; `git show :path` blobs | `true` / `Ok` for every entry |
| `hydrate` publish | agent `Decrypt`, then `hydrate_action`; all entries before any write | staged blob, worktree bytes via held dirfd, plaintext | `Ok(Publish)` for all; `Keep` untouched |
| `lock` flush | agent `Encrypt` (reseal), then `lock_action` | worktree bytes via held dirfd, staged blob, reseal output | `Ok(Flush)`; `Keep` untouched |
| Index record parsing (paths used as AD, regular-mode check) | `parse_index_entry` | each NUL-delimited `ls-files --stage -z` record | `Ok` (malformed/unmerged ⇒ refuse) |
| Protected file selection | `is_protected_path` | index path bytes | — |

The Lean lifecycle models (`Lifecycle.lean`) reproduce the hydrate, lock and
verify loops in this order. Review rule: a new effect in the adapter must
appear in this table with its gate, or it is a regression.
