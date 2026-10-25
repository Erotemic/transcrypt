# 09. Human-verifiable correspondence from Bash to specification

> **Historical planning context:** some requirements below were written
> before the 2026-10-25 maintainer direction. The current
> [v3 product charter](V3-PRODUCT-CHARTER.md) controls product goals,
> default UX, non-goals and review priorities; the
> [candidate wire specification](specs/V3-AUTHENTICATED-P0.md) controls
> existing ciphertext bytes. This document remains useful evidence,
> **not** an independent mandate for legacy/Bash parity or local-at-rest
> privacy in the Rust v3 product.

The Bash distribution is **not** formally verified by proving Rust correct.
Instead, this review maintains a deliberately limited, explicit claim:

> For the referenced Bash revision, the listed functions implement the
> independently specified operations under the stated Git/OpenSSL/OS
> assumptions, as checked by named reviewers and conformance tests.

This is a review record structure and initial function inventory, not a
completed review. A reviewer's name and sign-off cannot be prefilled.

## 1. Requirements-based mapping

Do not accept broad statements like "matches Rust." For each requirement
record the exact source commit and:

| Field | Required content |
|---|---|
| Spec obligation | R-xx, T-xx, exact subsection and formal definition |
| Entry point | Bash function, call graph, command-line selector |
| Source | Commit SHA, file path, line/range for that commit, relevant helpers |
| Inputs | Byte/string types, trusted/untrusted origin, env/config priority |
| Outputs | stdout vs stderr, stored Git object, config changes, file writes |
| Precondition | Required metadata, local credential, git mode, supported OpenSSL |
| Algorithm mapping | Every serialized byte, command option, KDF label, encoding and failure branch |
| Error | Exact exit status and zero-plaintext / rollback behavior |
| Assumptions | External tool version, platform, filesystem, concurrency |
| Evidence | Golden vector IDs, negative cases, associated bug reproducer |
| Review | Reviewer/date/decision, invalidation rule when code changes |

The review should enumerate *every* line of data-dependent behavior through
small enough named helper functions to hand-check, not merely grep for an
OpenSSL flag. In particular, shell word splitting, globbing, `$IFS`, trailing
newlines lost by command substitution, `set -e`, subshell exits and pipelines
may invalidate an apparently correct mapping.

## 2. Initial upstream/candidate source crosswalk

**Upstream base:** `elasticdog/transcrypt-v3` at
`fcf94da40f31110122577b857a1102ff4a486cf3`.
**Candidate:** October 2026 `transcrypt-v3-authenticated-pbkdf2-final-overlay.tar.gz`
applied over that base. Candidate function names are included for traceability
only; they are not approved protocol implementation.

| Review unit | Bash function(s) | Protocol/state section | Risk to check |
|---|---|---|---|
| Config read | `public_settings_file`, `read_public_setting`, `load_public_crypto_settings`, `validate_public_crypto_settings` | 02 sec 2-3 | Missing/duplicate keys, config path/symlinks, source snapshot precedence |
| Config generation | candidate `write_v3_config`, `select_v3_parameters` | 02 sec 3-4; 03 sec 5 | Entropy, salt, overwritten files, secure path creation |
| Key derivation | candidate `v3_hmac_hex`, `v3_load_keys`, `v3_load_context_keys` | 02 sec 4 | Exact transcripts, effective salt truncation, argv/env exposure, domain separation |
| Byte sealing | candidate `v3_encrypt_file` | 02 sec 4-5 | Format bytes, deterministic IV, authentication, temp files, empty blob semantics |
| Byte opening | candidate `v3_decrypt_file` | 02 sec 4-5 | Strict grammar, constant-time tag check, no partial stdout, no fallback |
| Clean/smudge/textconv | `git_clean`, `git_smudge`, `git_textconv` | 03 sec 3-4 | Fallback, already-encrypted-looking plaintext, stderr/stdout, cache behavior |
| Stage hook | `git_pre_commit`, `_list_encrypted_files`, `get_contexts_from_git_attributes` | 03 sec 1, 7 | Validate *staged* metadata and MAC, NUL-delimited names |
| Init and save | `gather_repo_metadata`, `save_configuration`, `save_helper_hooks`, `save_helper_scripts` | 03 sec 5-7 | Wrong-password persistence, mutable filters, symlinks |
| Rekey/migrate | `stage_rekeyed_files`, candidate `migrate_to_v3` | 03 sec 6 | Actual decryption, index atomicity, contexts, failure recovery |
| Cache/flush | `remove_cached_plaintext`, `flush_credentials`, `uninstall_transcrypt` | 03 sec 6-7 | Named notes refs, dangling plaintext, future cache disabled |
| Merge/Git aliases | `git_merge`, `list_files`, `show_raw_file`, context registry helpers | 03 sec 3-7 | Worktree/merge correctness; no plaintext in objects |

## 3. Review a crypto command down to bytes

For each invocation of `openssl`, `git`, `base64`, `sed` or other external
command, document:

1. The exact argument vector and whether *secret* data appears in argv/env.
2. The exact stdin source, binary-safe transport, and newline behavior.
3. Expected stdout/stderr and handling of output on nonzero exit.
4. OpenSSL/LibreSSL version and capability behavior tested; if unsupported,
   ensure the command fails closed without partially modifying state.
5. Whether a Bash local/subshell/pipeline changes error propagation.
6. Temporary file mode, directory, cleanup, symlinks and failure cleanup.
7. Relation to specification bytes and independent golden tests.
8. Which source paths could be injected or modified by untrusted Git data.

The proof of a pure Rust spec says nothing about these shell I/O details;
this checklist is essential to the weaker Bash assurance argument.

## 4. Traceability review template

When work starts, create **one review row per function/requirement edge**
using this template in a new reviewed ledger. The following is deliberately
*not* a signed review:

```text
Requirement ID:
Protocol version:
Bash source SHA:
Function and caller(s):
Inputs and explicit assumptions:
Required output on success:
Required output and state on failure:
Spec step -> command and byte transformation:
Potential side effects and secret exposure:
Corresponding vector and adversarial tests:
Known exceptions / deviations:
Reviewer/date:
Disposition: NOT REVIEWED | PASS | BLOCKED
```

A CI job may check that every exported Bash function has coverage links, but
no automatic tool is authorized to mark `PASS` for a human security review.
Any change to source, external dependencies, filter dispatch, versioned
config precedence, or spec invalidates its affected review rows.

## 5. Demonstrating correspondence with independent evidence

- Freeze specification and fixed vectors **before** implementations are
  changed to match them.
- Test Bash against independently computed vectors and invalid-input corpus.
- Test Rust against those same vectors *and* generated Lean model behaviors.
- Run bidirectional Bash/Rust seal/open and stage/clone workflows.
- Investigate every disagreement as a possible spec or implementation bug;
  never silently adjust expected values just to get green tests.
- Review Bash code's command-by-command correspondence and note external
  assumptions; maintain stronger proof statements only for proven Rust scope.
- Keep security claims conditional: a review and finite tests do not amount
  to complete formal verification of the Bash interpreter or OpenSSL CLI.

## October 24 2026 staged-index review amendment

The previous path enumerator regression did not establish correct *staged*
semantics. Two further bypasses were reproduced before this amendment:

- Stage protected `.gitattributes` and a plaintext blob directly in Git's
  index, then remove the matching filter only from the worktree attributes.
  The old hook examined worktree attributes and accepted the plaintext commit.
- Stage a regular plaintext blob and then replace the worktree file with a
  symlink. The old hook used `[[ -L path ]]` on the worktree and skipped the
  staged regular blob.

The updated `git_pre_commit` calls `_list_encrypted_files '' cached`, which
uses `git check-attr --cached` (index `.gitattributes`). It queries staged
file mode via `_staged_path_mode` and checks staged blob contents via
`_staged_file_looks_encrypted`. It refuses to treat enumeration errors as an
empty protected-path set, and uses NUL-delimited path records throughout.

Regressions are in `tests/{v2,v3}/test_staged_index.bats`. The hook is still
**local and bypassable** (`--no-verify`, disabled filters, alternate tools),
and v2's marker-only check cannot establish cryptographic authenticity. The
new implementation is not an atomic transaction across concurrent index
writers. Local/global/info Git attributes may be uncommitted configuration
and do not automatically become portable repository policy. These boundaries
must remain explicit until a reviewed v3 format and server-side enforcement
mechanism exist.

**Further local-override attack and fix:** `git check-attr --cached` does
not ignore `.git/info/attributes` or global attribute configuration. A local
`secret -filter` entry suppressed a staged `secret filter=crypt` rule and
allowed plaintext to commit. The hook now gathers both the effective local
view and an independently isolated staged index/object-store view using a
fresh temporary Git directory with no local/global attributes. It checks
the union of paths requiring encryption. This remains a cooperative hook:
local overrides that *add* protection are validated, but the presence of
locally configured attributes does not make those settings portable to other
clones. Linked-worktree compatibility is tested in a smoke check; complete
Git version/platform coverage remains an acceptance gate.
