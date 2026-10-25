# Transcrypt v3: internal security review (roadmap stage V6)

**Date:** 2026-10-25. **Scope:** the experimental Rust v3 profile on
`work/m2-nul-safe-path-enumeration`: `transcrypt-v3-core` (verified core),
`transcrypt-v3` (crypto adapter, credential agent, Git adapter), the wire
spec [V3-AUTHENTICATED-P0](specs/V3-AUTHENTICATED-P0.md). **Status:** an
internal review by the implementers. It does **not** replace the independent
external review (R-01) required before security-sensitive use.

Findings are rated **Accepted** (documented limitation within the stated
threat model), **Fixed**, or **Open** (should be addressed before a release).

## 1. Cryptographic construction and parameters

| Item | Assessment | Rating |
| --- | --- | --- |
| AES-256-CMAC-SIV (RFC 5297), 64-byte key, deterministic | Misuse-resistant deterministic AE; determinism is required so Git sees stable blobs. Ordered AD `[domain, config, path]` binds every record to its repository config and exact path; domain strings separate config tags from file records. | Accepted |
| Equality leakage | Identical plaintexts at the same path and config give identical ciphertexts; history reveals when a secret did *not* change. Inherent to deterministic encryption in Git. | Accepted, documented |
| Config tag = SIV encryption of the empty plaintext under `[config domain, prefix]` | Verified by *opening* it with the same AEAD (library constant-time compare); no hand-written tag comparison remains. Tag also serves as a passphrase verifier: an attacker with the public config can run an **offline guessing attack**, slowed only by Argon2id. | Accepted; passphrase ≥ 16 bytes enforced |
| Argon2id v1.3, m = 64 MiB, t = 3, p = 1, 32-byte random salt per repository | Matches RFC 9106's second recommended profile apart from lanes (p = 1 is conservative for single-thread use). Fixed in the format; no parameter negotiation and so no downgrade. | Accepted |
| Config identifier = SHA-256(config)[0:16] | Public discriminator only; authenticity comes from the AD, which contains the full config. A collision would not let a record open under another config. | Accepted |
| Nonce misuse / randomness | No nonces. Randomness is used once (salt, `getrandom`). | Accepted |
| Profile freeze | The path-bound AD superseded an earlier experimental two-component-AD draft *without* changing the record header. Records from that draft cannot be silently reinterpreted: SIV with a different AD fails authentication and releases nothing. **Decision:** freeze the current bytes as v3 profile 1 (`TV3F 00 01`, `TCFG3 00 01`). Any future change to AD, KDF or suite must change the magic version byte. | Fixed (decision recorded) |

## 2. Implementation of the cryptographic boundary

| Item | Assessment | Rating |
| --- | --- | --- |
| RustCrypto `aes-siv 0.8.0`, `argon2 0.6.0`, `sha2 0.10.9`, pinned with `=` | Byte-identical to independent OpenSSL/argon2-cffi vectors; `aes-siv` has had no independent audit. | Open (external review) |
| `Keyed` realizes the Lean `Realizes` contract | Each clause tested on the production primitive (`keyed_satisfies_the_realizes_contract`). | Accepted (A5) |
| Key-schedule zeroization | `aes-siv`, `aes`, `cmac` and `ctr` are built with their `zeroize` features (requires `zeroize 1.9.1`), so per-operation AES/CMAC/CTR key schedules are wiped on drop. | Fixed (this review) |
| Decrypted plaintext buffers | `decrypt_file` returns `Zeroizing<Vec<u8>>`; the agent zeroizes request bodies and responses; the core zeroes its output buffer on authentication failure (proved). AES-SIV now runs in place in caller buffers, so no library-internal heap copy of plaintext exists; agent responses, filter input and worktree reads are `Zeroizing` in clients too. | Fixed (H-5) |
| Argon2id working memory | `argon2 0.6.0` was built without `zeroize`, and even with it frees its 64 MiB of blocks (which determine the key) unwiped. Derivation now uses caller-owned memory wiped on drop, with the `zeroize` feature for its internal hashes. | Fixed (H-4) |
| Dependency advisories | RustSec database checked 2026-10-25: no advisory affects the locked versions. The two recent constant-time advisories in the SIV tag-comparison path (RUSTSEC-2026-0385 `ctutils`, RUSTSEC-2026-0003 `cmov`) are fixed in the locked `ctutils 0.4.5` / `cmov 0.5.4`. CI runs `cargo audit --deny warnings`. | Accepted (monitored) |
| Differential assurance | `v3_differential.rs` compares `Keyed` with OpenSSL AES-SIV and reference Argon2id on 22 lengths across every block boundary and random raw-byte paths, plus exhaustive tampering, truncation, extension and context changes. | Fixed (H-6) |

## 3. Key handling and the credential agent

| Item | Assessment | Rating |
| --- | --- | --- |
| Key never on disk | Derived after authentication, sent once over a private stdin pipe to the agent; never in argv, environment, socket traffic or files. Legacy on-disk key files are refused. | Accepted (tested) |
| Same-UID access | Any process running as the user can connect to the 0600 socket and decrypt or encrypt while unlocked, or replace the socket with its own listener and observe plaintext sent for encryption. Same-UID processes are inside the trust boundary. | Accepted, documented |
| Other-UID access | The session directory and socket must now be owned by the effective UID (previously only modes were checked), and both client and agent refuse a peer of another UID (`SO_PEERCRED` / `getpeereid`), so a socket reachable some other way cannot be used or impersonated across users. The agent also has a write timeout. | Fixed (H-8) |
| Agent authorization | Every request carries the full public config, compared with the config authenticated at startup, and must name a canonical protected path (proved, `authorize_agent_request_spec`). Hostile frames are refused without killing the agent (tested). | Fixed |
| Denial of service | Single-threaded agent with 120 s timeouts; a same-UID client can stall it. | Accepted |
| Swap, core dumps, debugger access | Every v3 process sets `RLIMIT_CORE=0`; on Linux it is also non-dumpable (`PR_SET_DUMPABLE=0`), which denies same-UID `ptrace` attach and `/proc/PID/mem` reads of the agent (tested via root-owned `/proc` entries). The agent `mlock`s its key page when `RLIMIT_MEMLOCK` allows. Per-operation key schedules are not locked; hibernation images are out of scope. | Fixed (residual: root, hibernation) |

## 4. Git and filesystem adapter

| Item | Assessment | Rating |
| --- | --- | --- |
| Malicious cloned repository | Hooks and Git config are not cloned. Hostile `.gitattributes` overrides (nested, `.git/info/attributes`) are caught by the proved `check-attr` gate. Symlinked `.transcrypt/config`, `.transcrypt/`, protected files or parents are refused. A hostile config with a chosen salt reveals nothing about the passphrase beyond what any config does. | Accepted |
| Transplanted, foreign, truncated or forged records | Refused before plaintext release (proved, `open_record_spec`; tested against real Git). | Fixed |
| Crash during `hydrate` | Previously left plaintext temporaries next to protected files, outside the `*.secret` filter, where `git add -A` would commit them unencrypted. Temporaries now live in `.git/transcrypt-v3-staging` (0700, symlink refused), stale ones are purged, and renames are fsynced. | Fixed (this review) |
| Crash during `lock` | Resumable: already-flushed files are recognized (`LockAction::Keep`); the key is kept until every file is flushed. | Accepted (tested) |
| Same-UID path races (TOCTOU) | Protected paths are resolved once with `openat(O_NOFOLLOW\|O_DIRECTORY)` per component; reads, staging writes and `renameat` use the held directory fds, so swapping a parent for a symlink after resolution cannot redirect a write outside the repository (unit-tested). A changed file is no longer overwritten (stamp check, H-7); a same-UID process can still win the window between that check and the rename. | Fixed (narrowed; residual race accepted) |
| Long repository paths | The agent socket was bound by absolute path and failed beyond the 104/108-byte `sun_path` limit. All processes now run from the repository root and use the short relative address. | Fixed (this review, tested) |
| Failed `init` | Left `.transcrypt/`, `.gitattributes`, hook and filters behind, blocking a rerun. Now rolled back precisely (only what this run created). | Fixed (this review, tested) |
| Plaintext file permissions | Git never writes plaintext readable by others: smudge releases plaintext only under a private umask and otherwise leaves ciphertext for the hooks/`hydrate` to publish at 0600 (H-16). Files the user creates follow their umask until `hydrate` makes them private; `status` warns. | Fixed (residual: user-created files) |
| Hook bypass | `--no-verify` commits, merges and rebases are now caught by the `pre-push` audit; `git push --no-verify` and checkouts without hooks need a server-side `audit` (H-3). The clean filter (`filter.required=true`) still encrypts everything it processes. | Mitigated; residual A13 |
| Rollback | An adversary controlling history can restore older valid records. No freshness state. | Accepted (non-goal) |
| Linked worktrees, submodules, `.git` files | Linked worktrees are supported (H-26): one agent per repository, private staging per worktree, and `lock` flushes every worktree before stopping the agent. A v3 repository can be a submodule (tested). | Fixed |

## 5. Hardening campaign, second pass (2026-10-25)

An adversarial pass over the adapter treated the earlier review as
hypotheses. Each finding below was reproduced against the previous code
with disposable repositories and synthetic secrets; each fix has a
regression test that fails on the old implementation.

| ID | Severity | Finding | Fix and evidence |
| --- | --- | --- | --- |
| H-1 | **High** | **Plaintext staged by `unlock`.** Hydration refreshed Git's stat cache with `git add -- <path>`, which Git reads as a *pathspec*. A hostile commit adding `sub/[a].secret` (a glob) and `sub/.gitattributes: a.secret -filter` made `unlock` stage an untracked plaintext `sub/a.secret` unencrypted into the object database, and report "changed nothing". Names like `:(glob)*.secret` behave the same. | Re-index only the verified paths with `git update-index -z --stdin` (raw paths, cannot add files); all Git subprocesses run with `GIT_LITERAL_PATHSPECS=1`. Test `hydration_never_stages_untracked_files_through_pathspec_magic`. |
| H-2 | Medium | **Wrong object read by revision syntax; index TOCTOU.** Staged objects were read with `git show :<path>`; a protected file named `0:a.secret` was read as stage 0 of `a.secret` (fail-closed DoS). Each `git show` also re-resolved the index after verification. | All objects are read with `git cat-file blob <oid>` using object ids from one parsed snapshot; ids are checked by the proved `is_object_id`. Replace refs are disabled. Test `staged_objects_are_read_by_object_id_not_revision_syntax`. |
| H-3 | **High** (deployment) | **Plaintext reaching the remote outside `pre-commit`.** Merges, rebases, cherry-picks, `--no-verify` commits, and clones that never ran `unlock` (no filter at all) commit plaintext `*.secret` files that nothing checks before push. | New keyless `audit` command (works in bare repositories and CI) and an installed `pre-push` hook auditing pushed commits; authenticates records when unlocked. Test `pre_push_and_audit_refuse_plaintext_in_history`. Residual: deployments without the hook or a server-side audit (A13). |
| H-4 | Medium | Argon2id memory (key-determining) freed unwiped. | See section 2. |
| H-5 | Low | Heap copies of plaintext inside AES-SIV and in clients; passphrase buffer could reallocate. | In-place SIV, `Zeroizing` buffers, preallocated passphrase buffer. |
| H-6 | — | Primitive assurance relied on three vectors. | Differential corpus, see section 2. |
| H-7 | Medium | **Lost edits.** An edit made between `lock`'s check and its flush (or `hydrate`'s check and publish) was silently overwritten; concurrent `hydrate`/`lock` runs could purge each other's staging files. | Replacement requires the file's stamp (dev, inode, size, mtime, ctime) from the check that justified it; `hydrate`/`lock` hold an exclusive `flock` on the staging directory. Tests `replacement_refuses_a_file_changed_since_it_was_checked`, SIGKILL fault injection. |
| H-8 | Low | Session ownership and peer identity unchecked. | See section 3. |
| H-9 | Medium (usability → security) | **Locked checkouts were unusable**, encouraging `--no-verify` and filter removal: the pre-commit hook refused *every* commit while locked; after `lock`, Git's stale stat cache re-ran the clean filter, so `git status`, `commit -a` and checkout failed. | Clean is idempotent on records that authenticate at their path (what Git expects of filters); while locked, both filters pass a record envelope of this config through unchanged and refuse everything else; `lock` re-indexes before stopping the agent; locked `verify-index` checks envelopes. Plaintext still cannot be cleaned while locked. Test `locked_pre_commit_checks_envelopes_and_allows_other_commits`. |
| H-10 | Low | Git checkout writes plaintext with the umask. | `hydrate` now makes already-decrypted protected files private (via an `O_NOFOLLOW` descriptor); `status` warns. Test `hydrate_makes_existing_plaintext_private`. |
| H-11 | Low | `pre-push` input over 1 MiB would have been truncated (found while reviewing this campaign's own code before commit). | Oversized input is refused. |
| H-12 | Medium | `init` in a repository already tracking `*.secret` files left them plaintext in the index and history while v3 appeared enabled. | `init` refuses while a `*.secret` path is in the index or `HEAD`. Test `init_refuses_secrets_already_tracked_in_plaintext`. |
| H-13 | Medium (availability) | `audit` used `ls-tree --format` (Git ≥ 2.36), so on Git 2.34 the installed `pre-push` hook would refuse every push. | Default `ls-tree` records are rewritten to the verified parser's shape; CI runs on Git 2.34. |
| H-14 | Low | The long-lived agent kept every descriptor it inherited from `unlock`'s caller (a pipe it held open could hang a script waiting for EOF). | The agent closes inherited descriptors beyond stdio at startup. Test `agent_does_not_keep_inherited_descriptors`. |
| H-15 | Medium | Editor and merge copies of secrets (`a.secret~`, `.a.secret.swp`, `a.secret.orig`, `#a.secret#`) hold plaintext but do not end in `.secret`, so `git add -A` committed them unencrypted and `audit` did not look at them. | `init`/`unlock` add ignore patterns to `.git/info/exclude`; `status` warns; `verify-index` (pre-commit) and `audit`/`pre-push` refuse such names (a heuristic backstop). Test `editor_and_merge_copies_of_secrets_are_caught`. |

### Third pass (2026-10-25)

| ID | Severity | Finding | Fix and evidence |
| --- | --- | --- | --- |
| H-16 | **High** | **Git wrote decrypted secrets readable by other users.** With `umask 022`, an unlocked `git checkout`/`switch`/`merge`/`rebase`/`restore` wrote smudged plaintext as mode 0644 (reproduced). The previous answer was a documentation requirement (`umask 077`). | Structural: smudge releases plaintext only when the umask it inherits from Git (the one Git applies to the file) is private. Otherwise it emits the authenticated record, and `post-checkout`/`post-merge`/`post-rewrite` hooks run `hydrate --auto`, which writes 0600. Test `git_never_writes_plaintext_readable_by_others` covers checkout, merge, rebase, stash, stash pop, restore, and a private umask. |
| H-17 | Medium (usability → safety) | Hydrate refused everything if any one protected file differed from the staged version or its plaintext. A user with one edited secret could not hydrate the rest; restored or stash-popped records could never be decrypted. | Hydrate decrypts exactly the files that are authentic records for their path and leaves all others untouched. Only files holding the staged plaintext are re-indexed, so an edit is never staged or overwritten. The Lean model (`hydratePlan_spec`) is re-proved for the new rule: every replaced file was an authentic record at its path, replaced by exactly its plaintext. |
| H-18 | Medium (availability) | **Unbounded Git output and audit work.** Subprocess output (`rev-list`, recursive `ls-tree`, `ls-files`) was collected without limit. `audit` listed the full tree of every commit (cost = commits × tree size), so a large or hostile push could exhaust a server hook. | Output is capped at 256 MiB (producer killed) and stderr is drained and capped. `audit` streams `rev-list` and checks only each commit's changes against its first parent (full tree for root commits and config changes). `--max-commits` sets a budget; the pre-receive hook defaults to 20000. Tests: endless producer killed, merge-introduced plaintext detected with only the merge selected, config change re-checks all records, budget refusal. |
| H-19 | Medium (deployment) | Missing or overridden local protection was undetectable (a deleted hook, `core.hooksPath`, `filter.<d>.process` or `required=false`, an info-attributes override), as was an unprotected remote. | `transcrypt-v3 doctor` checks each protection and exits non-zero. `contrib/v3/check-remote-enforcement` pushes a non-secret canary to confirm that a remote rejects plaintext; auth or network failures are reported as inconclusive, never as protected. Tests `doctor_detects_missing_protection`, `remote_enforcement_check_detects_unprotected_remotes`. |

| H-20 | Medium (usability → safety) | **Per-file filter processes made v3 slow enough to tempt bypasses.** Each file spawned a filter that also spawned `git rev-parse`. Release timings for 300 secrets: `git add` 4.1 s, `lock` 5.5 s, `unlock` 5.8 s, a decrypting checkout 9.5 s. | Git's long-running filter protocol, with pkt-line lengths decoded by the verified core (`decode_pkt_len`): 0.25 s, 1.4 s, 1.8 s and 1.7 s. Tests `long_running_filter_protocol` (handshake, round trips, path binding, oversized and malformed input) plus every real-Git test, which now runs through it. |
| H-21 | Low | A truncated final record (missing NUL) in `ls-tree`/`diff-tree` output was accepted. Found by the new randomized parser test; Git never emits it. | Listings must be NUL-terminated; diff-tree statuses are limited to A/M/T/D. |

| H-22 | Medium (data loss) | `init` read a terminal passphrase once: a typo encrypted everything under a passphrase nobody knows, unrecoverable after `lock`. | A new passphrase is asked for twice on a terminal (`init`, `rekey`). |
| H-23 | Medium (product gap) | No way to rotate a passphrase (a suspected leak left users stuck) and no safe uninstall. | `rekey` (one staged change, refuses uncommitted edits, agent switched only after staging; test `rekey_rotates_the_passphrase`) and `uninstall` (locks first, leaves ciphertext, removes only what v3 installed; test `uninstall_removes_v3_and_leaves_only_ciphertext`). |

| H-24 | Medium (usability) | **Secrets could not be merged.** Concurrent edits produced a binary conflict with only "ours" visible. A deleted or sparse protected file, or an unmerged index, made `hydrate`, `unlock`, `lock` and `status` fail for every file. | A merge driver (decrypts authenticated inputs, merges in a private directory, re-encrypts); conflict-aware `hydrate`/`status`; missing files skipped. Tests `secrets_merge_as_plaintext` (clean and conflicting merges under umask 022 and 077) and `deleted_protected_files_do_not_block_lock_or_hydrate`. |

| H-25 | Low (usability) | `git diff` of a secret showed only "Binary files differ". The Bash approach (a textconv cache) keeps plaintext in `refs/notes`, and textconv cannot authenticate path-bound records (it gets no full path). | An external diff driver: each side is authenticated at its own path, plaintext stays in the private scratch directory only while `diff` runs, and nothing is cached. Test `git_diff_shows_decrypted_changes`. |

| H-26 | Medium (usability) | `git worktree add` in a v3 repository failed outright (the filter refused linked worktrees, so Git aborted). `unlock`/`lock` were not idempotent: a second `unlock` failed, and `lock` without an agent failed even with no plaintext left. | Worktree support. In a multi-worktree repository, `lock` refuses while any worktree holds an edit, and stops the agent only after flushing all of them. Idempotent `unlock`/`lock`. Tests `linked_worktrees_share_one_unlocked_session`, `unlock_and_lock_are_idempotent`. |

| H-27 | Medium (stale key in memory) | After pulling a collaborator's `rekey`, the agent kept the obsolete key indefinitely: `unlock` with the new passphrase refused ("an agent is running"), and `lock` reported "Already locked" while that agent kept running, since a stop must carry the agent's own config. | An agent that refuses a request while its own worktree config has changed knows its key is obsolete and exits. `unlock` gives such an agent a moment to exit before reporting a genuine conflict (another worktree's config). Test `pulled_rekey_retires_the_stale_agent`. |

Re-attacking the earlier fixes found no further exploit:
- **Pathspec staging:** only `update-index -z --stdin` paths remain, and they come from the verified snapshot.
- **difftool/mergetool temporaries:** written through smudge, so the umask rule now covers them.
- **Merges of plaintext:** smudge refuses them while unlocked.
- **Agent:** frame and size bounds are unchanged.

**Crash safety evidence.** `killed_lock_and_hydrate_never_corrupt_or_leave_plaintext_behind`
SIGKILLs `lock` and `hydrate` at twelve points over 22 protected files.
After every kill each file is exactly its ciphertext or its plaintext, no
other file has appeared in the worktree, and rerunning converges (with a
clean `git status` after hydrate).

**Claims that can and cannot be made.**

- *Can:* the production decision core and codec are machine-checked against
  an independent spec (relative to the primitive contract). The adapter
  reads every Git object through ids from one verified snapshot, never
  stages through pathspecs, and never replaces a worktree file that changed
  since it was checked (up to a same-UID race window). Plaintext is released
  only after authentication at its exact path and config. Plaintext cannot
  be cleaned into the index while locked. Pushed history is audited by the
  installed hook.
- *Cannot:*
  - Full formal verification of the product.
  - Security against processes running as the same user.
  - Prevention of plaintext commits in checkouts that never installed the
    filters, unless a server-side `audit` is deployed.
  - Rollback resistance.
  - Hiding equality of plaintexts at a path.
  - Independent review: still outstanding (R-01).

## Review package

For the external review (R-01), in reading order:

1. Protocol and bytes: [V3-AUTHENTICATED-P0](specs/V3-AUTHENTICATED-P0.md).
2. Threat model, assumptions, ranked risks: [V3-ASSUMPTIONS](V3-ASSUMPTIONS.md).
3. Proofs: [PROOF-STATUS](../../proofs/aeneas/v3/PROOF-STATUS.md),
   [V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md); independent spec
   `proofs/lean/Transcrypt/V3Policy.lean`.
4. Implementation map: core `rust/crates/transcrypt-v3-core/src/lib.rs`;
   primitives `rust/crates/transcrypt-v3/src/lib.rs` (`Keyed`,
   `derive_key`, `clean_file`); adapter `src/{main,git,worktree,setup,audit}.rs`; agent
   `src/session.rs`; fd-relative filesystem `src/fsat.rs`; adapter call-site
   table in V3-ASSUMPTIONS.
5. Adversarial evidence: `rust/crates/transcrypt-v3/tests/{adversarial,git_lifecycle}.rs`.
6. Cryptographic evidence: `tests/v3/reference/{check_vectors,differential}.py`,
   `rust/crates/transcrypt-v3/tests/{v3_vectors,v3_differential}.rs`; this
   document, sections 1–2.
7. Requested focus: AES-SIV AD construction and the config-tag-as-verifier
   design; `aes-siv` crate; the locked-filter envelope pass-through (A14);
   the adapter's Git invocations (A4/A7).

## 6. Reproducibility

- Rust: `Cargo.lock` tracked, crypto crates pinned with `=`; CI runs the full
  workspace tests on Ubuntu and macOS. The adapter's FFI was additionally
  type-checked for `aarch64-apple-darwin` locally.
- Proofs: Lean, Aeneas, hax and mathlib pinned; extraction reproduced
  byte-for-byte with cargo-hax 0.4.2; CI re-extracts, rebuilds and audits
  axioms.

## Summary

No known vulnerability remains within the stated threat model (a non-root
attacker controlling the Git remote and history but not the user's Unix
account), given a deployment that runs the `pre-push` hook or a server-side
`audit` (A13). The release blocker is an external cryptographic and adapter
review (R-01), including the unaudited `aes-siv` crate.
