# V3 traceability and refinement targets

This correspondence table refers to the independent
[`V3-AUTHENTICATED-P0.md`](../specs/V3-AUTHENTICATED-P0.md). Rust code
must be changed to comply with that contract, not vice versa.

| Protocol clause | Production Rust | Independent conformance evidence | Planned Lean obligation |
|---|---|---|---|
| Config bytes 0..54, magic, salt, verifier | `transcrypt-v3-core::{encode_config_prefix,encode_config,parse_config}` | core unit tests, `vectors.tsv` | Extracted parser/encoder roundtrip under canonical sizes |
| File header bytes 0..21, minimum 38 | `transcrypt-v3-core::{encode_file_header,parse_file_header}` | core unit tests, Rust negative tests | Header construction/parse refinement |
| Argon2id v19 fixed params/64B key | `transcrypt-v3::derive_key` | Python argon2-cffi vector | External Argon2id semantics assumption |
| Deterministic AES-SIV file authentication | `transcrypt-v3::{encrypt_file,decrypt_file}` | Python OpenSSL-backed AESSIV vectors | External AES-SIV correctness and unforgeability assumptions |
| Metadata binding and fail closed | `authenticate_config`, `config_id`, `decrypt_file` | config tampering and wrong password tests | No successful open with invalid authentication |
| Credential authorization | `main::unlock` and `session::{start,serve}` | Git wrong-password no-agent test and no-disk-key assertion | Preflight-before-persistent-effects adapter relation |
| Staged tree safety | `main::verify_index`, Git hook | forged raw Git object regression | Index truth, symlink, and ciphertext-refinement effect contract |
| Clone hydration | `main::{hydrate,publish_plaintext}` | Git clone, staged-only index, multi-file preflight, and repeated hydration tests | No destructive action before all inputs pass; worktree bytes equal authenticated ciphertext or plaintext |
| Lock | `main::lock` and `session::stop` | full lifecycle and dirty-file rejection test (to expand) | Credential removal only after full encrypted flush |

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
