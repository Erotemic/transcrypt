# Transcrypt v3 secure-first proof of concept: canonical byte contract

**Status:** Proposed experimental v3 protocol. No compatibility with released
legacy formats or the earlier `TCRYPT3:` experiment. The Rust implementation
must be built/tested and independently reviewed before security-sensitive use.
This document is **independent of the Rust source** and is the intended
reference for a future Bash implementation and Lean refinement proofs.

## Scope

One context, one protected filename policy (`*.secret`), one fixed crypto
suite, and these actions: `init`, `unlock`, `clean`, `smudge`, `verify-index`,
`hydrate`, `lock`, plus the read-only `status` and `help`. No migration, rekey, nested contexts, GPG, merge driver,
streaming files larger than 16 MiB, or implicit plaintext fallbacks.

## Constants and primitives

- Password KDF: **Argon2id v=19**, `m=65536 KiB`, `t=3`, `p=1`, `output=64 bytes`.
- Salt: 32 bytes from the operating system CSPRNG, generated once per repo.
- AEAD: **AES-256-CMAC-SIV** per RFC 5297, 64-byte key, **deterministic**
  (no nonce), 16-byte authentication tag followed by ciphertext.
- Associated data is an **ordered list** of bytestrings, not concatenated
  data. The order matters and follows RFC 5297 S2V.
- Config identifier: first 16 bytes of SHA-256 of the **complete committed
  config bytes**; identifier is only a fast public discriminator, not an
  authentication mechanism.
- Maximum plaintext: 16 MiB. Reject oversized input before crypto.
- A wrong version, wrong password, wrong config, or corrupt ciphertext
  always **fails**; never pass through original bytes as plaintext.

## Committed `.transcrypt/config`

Fixed length **55 bytes**; no variable configuration parsing:

| Offset | Length | Contents |
|---|---:|---|
| 0 | 7 | ASCII `TCFG3`, then `00 01` |
| 7 | 32 | random repository salt |
| 39 | 16 | AES-SIV encryption of empty plaintext |

Compute key `K = Argon2id(passphrase, salt, 65536, 3, 1, outLen=64)`.
Let `prefix = config[0:39]`. The final 16-byte authenticator is:

`AES-SIV(K).encrypt(plaintext=b"", AD=[b"transcrypt/v3/config", prefix])`

An unlock must validate the tag with the derived key **before** persisting
credentials, installing filters, or hydrating plaintext.

## Protected file object

`record = header || AES-SIV(K).encrypt(plaintext, AD)` where the header is:

| Offset | Length | Contents |
|---|---:|---|
| 0 | 6 | ASCII `TV3F`, then `00 01` |
| 6 | 16 | SHA-256(config bytes)[0:16] |
| 22 | 16+N | AES-SIV tag (16 bytes) followed by N ciphertext bytes |

`AD=[b"transcrypt/v3/file", complete_config_bytes, canonical_git_relative_path_bytes]`.

The third associated-data element is the **exact Git-relative pathname as
raw bytes**, as supplied by Git's `%f` expansion (for filters) or the
NUL-delimited staged index (for verification, hydration and locking). Valid
names have a nonempty `*.secret` basename, use `/` separators, are at most
4,096 bytes, and contain no NUL, empty component, `.` or `..` component.
No Unicode normalization, case folding, absolute paths or filesystem-based
canonicalization is performed: Git path bytes are the authoritative identity.
The credential agent rejects missing or noncanonical path input.

**Profile freeze (2026-10-25).** The bytes specified here are frozen as
*v3 profile 1*, identified by `TCFG3 00 01` and `TV3F 00 01`. Any future
change to the associated data, KDF parameters or suite MUST change the
version byte of the affected magic, so that no released record is ever
reinterpreted under a different profile.

This **path-bound v3 experimental profile supersedes** the earlier v3 P0
ciphertext profile that used only two associated-data components. Existing
old-profile ciphertext is NOT decryptable by this implementation. To avoid
accidental silent downgrade, there is no legacy fallback. Do not deploy this
over an initialized earlier v3 test repository without first exporting the
plaintext with the earlier binary, then reinitializing a fresh repository.

An empty plaintext is valid (`N=0`, total record length 38 bytes).
The selected AES-SIV mode is deterministic and **leaks equality of identical
plaintexts at the same Git path in the same repository**. Moving a record to
another protected pathname fails authentication, even if its format header,
config ID and tag are otherwise valid. Renaming a protected file therefore
requires decrypting and re-encrypting under its new Git pathname; merely
moving an encrypted Git blob is not safe. Repository/metadata substitution,
modification, cross-path replay and cross-repository ciphertext replay fail
unless the corresponding key and associated-data components also match. Old valid repository snapshots can still be rolled
back by adversaries controlling Git history; freshness requires separate
trusted state and is outside this POC.

## Stateful lifecycle and key management

- `init`: require an ordinary Git repository, no `.transcrypt` or
  `.gitattributes`, and no conflicting `pre-commit` or `pre-push` hook.
  Generate metadata, install Git filters, install the local `pre-commit`
  (`verify-index`) and `pre-push` (`audit` of the pushed commits) hooks, and
  stage the public config and
  `*.secret` attributes with `-diff` (no textconv cache). Explicitly committing those files is required.
- `unlock`: derive from a terminal passphrase or opt-in stdin, authenticate
  the config **first**, and send the derived key over a private one-way stdin
  pipe to a dedicated credential process. The process keeps it in memory.
  The only persistent endpoint is a mode-`0600` Unix-domain socket at
  `.git/transcrypt-v3/session.sock`, beneath a mode-`0700` directory.
  Git filters send operation, exact public config, canonical Git-relative
  pathname bytes, and plaintext/ciphertext bytes over the socket; the raw key is **never returned to clients**.
  The agent authenticates the supplied public config on every operation.
  Stale sockets left by dead processes may be reclaimed only after verifying
  the socket type and that it has no listening peer. Missing/dead agents fail
  closed. Earlier prototype on-disk keys must be removed or locked using the
  previous binary before starting this agent.
- `clean`: require the Git-provided `%f` path as a single argument and emit
  a complete path-bound authenticated record. Clean is **idempotent**, as Git
  expects of filters: input that already opens as a record at this path under
  this config is returned unchanged (by determinism, exactly the record that
  sealing its plaintext gives); any other recognizable v3 record is refused
  (no double encryption); everything else is sealed.
- `smudge`: authenticate including the Git-provided `%f` path and then
  release plaintext; reject all other bytes.
  Git diffs are disabled for protected files rather than invoking textconv.
- **Locked filters.** When no agent serves the worktree config, neither
  filter has the key, so neither can change a record: both output input that
  has the v3 envelope of this config (header with its config id, within the
  size bound) unchanged and refuse everything else. A locked checkout thus
  behaves like a clone that never ran `unlock` (ciphertext in the worktree;
  checkout, status and commits of other files work), and plaintext can still
  never be cleaned into the index. Authenticity of such records is checked
  when unlocked (`verify-index`, `hydrate`, `audit`).
- **Git object access.** Every staged or committed object is read by the
  object id from one `ls-files --stage -z` (or `ls-tree`) snapshot, through
  `git cat-file blob <oid>`, never by `:<path>` revision syntax (which reads
  `:0:x.secret` as stage 0 of `x.secret`). Object ids must be 40 or 64
  lowercase hex digits. Every Git subprocess runs with
  `GIT_LITERAL_PATHSPECS=1` and `GIT_NO_REPLACE_OBJECTS=1`. Blob reads stop
  at the 16 MiB record bound.
- `verify-index`: check staged `.transcrypt/config` exactly matches worktree
  config; staged `.gitattributes` equals the fixed policy; every index
  `*.secret` is a regular Git blob decryptable using the active config/key.
  While locked (as the `pre-commit` hook) it checks the record envelopes
  instead, which rejects every plaintext not deliberately formatted as a v3
  record. A Git hook only guards cooperating local commits; it is bypassable
  and does not enforce remote policy.
- `audit [<rev-list arguments>]`: for every commit selected (default
  `HEAD`), every `*.secret` tree entry must be a regular file whose blob has
  the v3 envelope of the `.transcrypt/config` committed in the same tree; a
  commit with protected files but no config is refused. Needs no key, so it
  can run in CI or a server-side hook, and catches plaintext committed by
  clones that never ran `unlock`. When the agent serves that config, each
  record is also authenticated at its path. The `pre-push` hook audits the
  pushed commits not already on the remote's tracking branches (merges,
  rebases, cherry-picks and `--no-verify` commits never ran `pre-commit`).
  A keyless audit cannot detect forged records that merely carry a valid
  envelope.
- `hydrate`: authenticate **every staged protected object** and confirm the
  staged metadata matches the worktree before exposing plaintext. Each
  protected worktree file must equal either its staged ciphertext or the
  authenticated plaintext of that ciphertext. Unexpected bytes or symlinks
  are rejected without modifying any file. For ciphertext-backed files,
  decrypt the staged object and publish plaintext through mode-0600 exclusive
  temporary files created in the private staging directory
  `.git/transcrypt-v3-staging` (a real mode-0700 directory; never the
  worktree, so a crash cannot leave plaintext where `git add` would commit
  it) and renamed with `renameat` into the protected file's parent directory,
  which was resolved once with `O_NOFOLLOW` per component. Stale staging
  files from an interrupted run are deleted. Do **not** invoke `git restore` or `git checkout`
  to hydrate: they would publish files one at a time through the smudge
  filter, outside this all-or-nothing preflight. Already-hydrated
  paths are left untouched, allowing retries after interrupted hydration.
  Compare the staged index snapshot before publication, and replace a file
  only if its stamp (device, inode, size, mtime, ctime) still equals the one
  read when it was checked. Afterwards re-index exactly the protected paths
  with `git update-index -z --stdin` (raw paths, never pathspecs, and never
  `--add`; `git add -- <path>` would read a tracked `[a].secret` as a glob
  and stage an untracked `a.secret`) so the clean filter refreshes the stat
  cache, and verify that the staged blob IDs and modes have not changed.
  Without that refresh, Git can report hydrated files as dirty because cached
  size and mtime still describe ciphertext. `hydrate` and `lock` hold an
  exclusive lock on the staging directory for their whole run. A same-UID
  writer can still race the final stamp check and the rename; multi-file
  atomicity is not claimed.
- `lock`: preflight no dirty or untracked protected files; overwrite tracked
  plaintext working files with the exact ciphertext in the index (only when
  resealing the worktree reproduces that ciphertext byte for byte, through
  the same private staging directory, and only if the file's stamp is
  unchanged since it was checked), re-index those paths while the agent still
  runs (clean returns the records unchanged, so a locked checkout is clean),
  and then terminate the credential agent. An interrupted `lock` is resumed
  by rerunning it. No derived-key file is written. This is NOT
  certified secure deletion, atomic across multiple files, or protection
  against plaintext in Git textconv notes, caches, process memory dumps,
  swap, snapshots, or backups.

Process and filesystem hardening: every v3 process disables core dumps and,
on Linux, is non-dumpable (no same-UID `ptrace` or `/proc/PID/mem` access to
the agent); the agent `mlock`s its key page where permitted. Protected paths
are resolved with `openat(O_NOFOLLOW)` per component and replaced with
`renameat` relative to the held directory descriptors. The session directory
and socket must be owned by the effective UID, and both client and agent
refuse a socket peer running as another UID (`SO_PEERCRED`/`getpeereid`).
Argon2id runs in caller-supplied memory that is wiped afterwards, and
AES-SIV encrypts and decrypts in place in caller buffers (no heap copies of
plaintext); passphrase buffers are preallocated and wiped. The agent socket is
bound and connected through the relative address
`.git/transcrypt-v3/session.sock` from the repository root, so deep
repository paths do not exceed the `sun_path` limit. Remaining limits: the
socket is usable by programs running as the same Unix UID (inside the trust
boundary), same-UID processes can race on file *contents*, multi-file
operations are resumable rather than atomic, files above 16 MiB are refused,
and rollback of Git history is not detected.

## Machine checkability and implementation correspondence

- `rust/crates/transcrypt-v3-core/src/lib.rs`: pure `no_std` implementation
  of the encoders, strict parsers **and every protocol decision**: path
  policy, configuration authentication, record sealing (including refusing
  inputs that already are v3 records) and opening (zeroing the output on
  authentication failure), agent request authorization, the `check-attr`
  verdict and the hydrate/lock actions. Cryptography enters only through the
  `V3Primitives` trait. Translated by Charon/Aeneas and proved against
  `proofs/lean/Transcrypt/V3Policy.lean`; see
  `proofs/aeneas/v3/PROOF-STATUS.md`.
- `rust/crates/transcrypt-v3/src/lib.rs`: KDF and AES-SIV adapter invoking
  external cryptographic libraries. Their algorithmic correctness and
  constant-time behavior are separate trusted assumptions.
- `rust/crates/transcrypt-v3/src/main.rs`: Git/OS adapter, to be tested under
  fault injection and eventually related to a transition specification.
- `tests/v3/reference/check_vectors.py`: independent Python reference using
  argon2-cffi and OpenSSL-backed `cryptography.AESSIV`; generates committed
  hex vectors in `vectors.tsv`, also consumed by Rust tests.
- `proofs/aeneas/translate-v3-core.sh`: reproducible translation entrypoint;
  the tracked extraction and its refinement proofs build in CI.

Bash correspondence: the released Bash 2.x and draft v3 script have **not**
been changed to support this format. They must implement exactly the same
ordered AAD and record grammar to become interoperable. Existing Bash
legacy behavior is not a requirement on this secure-first Rust implementation.

Correspondence and proof obligation map: [`v3-core-traceability.md`](../reference/v3-core-traceability.md).

## Local agent framing (adapter-only, not part of the committed wire protocol)

This is an internal IPC format and may change independently of ciphertext
format v3. Request: one ASCII opcode (`P` ping, `E` encrypt, `D` decrypt,
`X` shutdown), 55-byte exact public config, four-byte big-endian path length, that many raw canonical Git-relative
pathname bytes, four-byte big-endian body length, then that many payload
bytes. Ping/shutdown carry an empty path and body; encrypt/decrypt require a
validated path. Response: one-byte status (0 success, 1 error),
four-byte big-endian output length, then bytes. Both directions enforce a
16-MiB-plus-envelope bound. The agent verifies the supplied config bytes
match those authenticated on startup before processing any payload. The
credential is transferred solely via a 64-byte pipe during process startup.

Only the live credential agent performs encryption/decryption. It should not
be confused with a verified enclave: same-UID processes can use the socket,
OS process inspection and swap are outside the core proof boundary, and
start/stop plus Git file operations are not yet modeled transactionally.

### Effective staged filter policy (adapter acceptance contract)

Before `verify-index` reports success or `hydrate`/`lock` may proceed, each
protected tracked pathname MUST have effective staged Git attribute
`filter=transcrypt-v3`. The adapter MUST compute that attribute with Git's
own `check-attr --cached -z --stdin` semantics, not infer it solely from the
root `.gitattributes` blob; local info attributes and nested staged attributes
can override the root. Protected index entries MUST be ordinary 100644 files;
the staged root `.gitattributes` and `.transcrypt/config` MUST also have regular
file modes. A local hook is an integrity aid, not a server-side trust anchor.
