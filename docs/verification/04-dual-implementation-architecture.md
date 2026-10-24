# 04. Two implementations, one specification

The design is deliberately asymmetric in assurance, **symmetric in protocol**.
Bash remains the minimal runtime distribution. Rust is optional and may offer
stronger code-level assurance and a more convenient hardened secret-handling
implementation. Neither is authorized to define the protocol by its own
observed output alone.

## 1. Repository / release ownership proposal

- `docs/verification/`: this reviewed shared specification, requirement IDs,
  threat model, review evidence, vectors, and toolchain/proof contract.
- `transcrypt`, `contrib/*`, `tests/v2`, `tests/v3`: upstream-maintained Bash
  CLI/filter implementation and its existing test suite.
- `rust/` **or an independently released `transcrypt-rs` repository**:
  an optional distribution and its proof-aware crates. Whether the maintainer
  wants the Rust source in the primary repository is a packaging/governance
  decision, not a prerequisite for sharing the on-disk protocol.
- `proofs/` (eventual, perhaps Rust-only repository): independent Lean
  model, generated Aeneas files, refinement proofs, version-pinned tools.
  Generated code is build output, not the source of the normative spec.
- Release assets: existing Bash package unchanged in dependency footprint;
  separate Rust binary artifacts on supported platforms.

No Rust compile step, RustCrypto crate, Lean dependency, or Git LFS feature
may be required for installing or running the Bash distribution.

## 2. Rust crate boundaries (target layout, not created here)

```text
transcrypt-rs/
  crates/
    transcrypt-protocol/      pure byte parser/serializer, errors, context
    transcrypt-policy/        pure repo classification and transaction planner
    transcrypt-crypto/        crypto adapter to audited library primitives
    transcrypt-git/           Git/index/worktree/attributes adapter
    transcrypt-cli/           user-facing CLI, key input, process and I/O
  proofs/
    Spec/                    independent Lean semantics
    Generated/               Charon/Aeneas translation of supported pure crates
    Refinement/              proofs linking Generated to Spec
    Contracts/               opaque crypto/Git/fs/OS contracts
  tests/
    vectors/                 generated from the frozen spec, not from Rust
    interop/                 Rust/Bash cross-implementation tests
```

**Translate the actual released pure crate** with Charon/Aeneas. No
hand-written Lean duplicate may masquerade as a theorem about Rust. Keep the
pure crates safe, sequential, bounded and extraction-friendly; avoid
unsupported closures/nested loops/trait patterns in the first kernel. The
adapters may use ordinary idiomatic Rust but must have explicit contracts.

### Protocol crate

Exposes `decode_header`, `parse_config`, `canonicalize_config`,
`detect_format`, `encode_record`, `decode_record`, and structured errors.
The parser handles hostile byte arrays without panicking, overflow, or
surreptitious default values; output canonicalization is proven.

### Policy crate

Exposes `classify`, `select_operation`, `plan_init`, `plan_unlock`,
`plan_migration`, `plan_rekey`, and `check_stage`, with no actual I/O.
Models permissions/context mappings and produces a structured plan, not
shell commands. This is the next Aeneas proof target after the parser.

### Crypto adapter

Calls independently reviewed primitives in memory. It must not pass keys to
process argv or environment, and it must not expose plaintext until an
entire authenticated record has been checked. Cryptographic primitive
implementations are trusted until proved separately. All algorithms/
parameters come from the frozen spec; the adapter has no convenient
platform-specific fallback.

### Git and filesystem adapter

Accepts an immutable transaction plan; gathers exact byte-path Git state;
applies effects through a small, audited interface (snapshot, read-index,
check-attr, read-blob, write-temp-index, atomic-publication, rollback,
recovery). Checks assumptions about symlinks, `GIT_INDEX_FILE`, worktrees,
and concurrent mutation before publishing. Error reporting never carries
plaintext or credentials.

### CLI/credential adapter

Implements prompts, argument parsing, Git filter process invocation,
password-FD/TTY input and optional explicitly authorized local persistence.
Keep CLI stdout contracts separate from diagnostics and logs. The CLI must
be able to run in shell-driven Git filters with no interactive terminal.

## 3. Bash traceability design

Map each normative requirement to a Bash function, call sites, inputs,
external commands and failure semantics. Use a **function-and-commit-hash**
trace rather than depending on approximate line numbers. For initial review:

| Component | Upstream prototype / candidate functions | Relevant spec |
|---|---|---|
| Public metadata | `public_settings_file`, `read_public_setting`, `validate_public_crypto_settings`; candidate `write_v3_config` | R-06, R-10, R-11, R-17 |
| Crypto | candidate `v3_load_keys`, `v3_encrypt_file`, `v3_decrypt_file` | R-02..R-09 |
| Git filters | `git_clean`, `git_smudge`, `git_textconv`, `git_merge` | R-01..R-05, R-15 |
| Stage checks | `git_pre_commit`, `_list_encrypted_files`, `get_contexts_from_git_attributes` | R-10, R-11, R-15, R-18 |
| Credentials and init | `load_password`, `save_password`, `save_configuration`, `force_checkout`, main dispatch | R-09, R-12, R-16 |
| Migration and cleanup | candidate `migrate_to_v3`, `remove_cached_plaintext`, `flush_credentials`, `stage_rekeyed_files` | R-16, R-20..R-23 |

This table is a starting index, **not a passing audit**. Populate the
source-by-source review matrix in [09](09-bash-traceability-and-review.md)
only after the actual implementation changes land. Changing a reviewed
function (or its dependencies) invalidates the affected review until redone.

## 4. Features shared between distributions

| Feature | Bash | Rust | Consistency rule |
|---|---|---|---|
| Legacy decrypt / status | Already supported | Dedicated legacy adapter | Same compatible plaintext, carefully bounded parsing |
| Secure format clean/smudge | New work | New work | Exact same bytes for same key/context/plaintext/metadata |
| Empty/binary files | New test coverage | New test coverage | Same parser and ciphertext conventions |
| Named contexts | Existing feature | Required | Same context grammar and separation |
| Public config | Partial reader | New strict parser | Shared canonical subset and same fail behavior |
| Transactional init/unlock | Fix needed | Build from state model | Same success/failure semantics; no secret leaks |
| Migration/rekey | Fix needed | Build from state model | Same on-disk objects and recoverable failure semantics |
| Git hooks/index verification | Fix needed | Build | Same `StageOK` decision, even if hook interfaces differ |
| Cached plaintext handling | Fix needed | Must never create new plaintext notes | Same explicit retention claims |
| Process key handling | Requires redesign | In-process APIs | Both must meet release policy or explicitly fail unsupported |
| Auxiliary diagnostics | Concise actionable warnings | Matching or richer local messages | Never change filter stdout; avoid forcing new Bash commands |

## 5. Distribution and compatibility rules

- A collaborator with only Bash must be able to read/write objects made by
  the Rust CLI *when the format/suite is listed in the supported matrix*.
- A collaborator with only Rust must be able to read/write objects made by
  Bash. Test different OpenSSL/LibreSSL implementations on real Git clones.
- Unsupported crypto capability fails before modifying index, credentials,
  or filters; it does not fall back to an insecure format.
- Rust proof status is not a requirement for a Bash patch build to run tests.
  Rust/Lean CI is independent and can gate **Rust security assurance claims**,
  while Bash releases continue on their maintainer's approved workflow.
- Interoperability is defined by frozen vectors plus cross-clean/smudge and
  shared Git behavior. Same feature name or file extension is not sufficient.
