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
| Decrypted plaintext buffers | `decrypt_file` returns `Zeroizing<Vec<u8>>`; the agent zeroizes request bodies and responses; the core zeroes its output buffer on authentication failure (proved). Client-side Git filter memory is not zeroized (short-lived process). | Accepted |

## 3. Key handling and the credential agent

| Item | Assessment | Rating |
| --- | --- | --- |
| Key never on disk | Derived after authentication, sent once over a private stdin pipe to the agent; never in argv, environment, socket traffic or files. Legacy on-disk key files are refused. | Accepted (tested) |
| Same-UID access | Any process running as the user can connect to the 0600 socket and decrypt or encrypt while unlocked, or replace the socket with its own listener and observe plaintext sent for encryption. Same-UID processes are inside the trust boundary. | Accepted, documented |
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
| Same-UID path races (TOCTOU) | Protected paths are resolved once with `openat(O_NOFOLLOW\|O_DIRECTORY)` per component; reads, staging writes and `renameat` use the held directory fds, so swapping a parent for a symlink after resolution cannot redirect a write outside the repository (unit-tested). A same-UID process can still change a file's *contents* between our read and rename. | Fixed (narrowed; contents race accepted) |
| Long repository paths | The agent socket was bound by absolute path and failed beyond the 104/108-byte `sun_path` limit. All processes now run from the repository root and use the short relative address. | Fixed (this review, tested) |
| Failed `init` | Left `.transcrypt/`, `.gitattributes`, hook and filters behind, blocking a rerun. Now rolled back precisely (only what this run created). | Fixed (this review, tested) |
| Plaintext file permissions | `hydrate` publishes 0600 files, but Git's own checkout (smudge) and user-created files follow the umask, so decrypted secrets can be readable by other local users (outside the trust boundary). Git offers no per-file mode control. `status` now warns; the guide requires `umask 077`. | Accepted with mitigation |
| Hook bypass | `--no-verify` or a server without the hook is not checked; the clean filter (`filter.required=true`) still encrypts everything it processes. | Accepted, documented |
| Rollback | An adversary controlling history can restore older valid records. No freshness state. | Accepted (non-goal) |
| Linked worktrees, submodules, `.git` files | Refused (`repo_root`). | Accepted (unsupported) |

## 5. Reproducibility

- Rust: `Cargo.lock` tracked, crypto crates pinned with `=`; CI runs the full
  workspace tests on Ubuntu and macOS. The adapter's FFI was additionally
  type-checked for `aarch64-apple-darwin` locally.
- Proofs: Lean, Aeneas, hax and mathlib pinned; extraction reproduced
  byte-for-byte with cargo-hax 0.4.2; CI re-extracts, rebuilds and audits
  axioms.

## Summary

No known vulnerability remains within the stated threat model (a non-root
attacker controlling the Git remote and history but not the user's Unix
account). The release blocker is an external cryptographic and adapter review (R-01),
including the unaudited `aes-siv` crate.
