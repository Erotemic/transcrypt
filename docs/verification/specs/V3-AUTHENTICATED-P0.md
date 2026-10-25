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
  `.gitattributes`, no conflicting `pre-commit` or `pre-push` hook, and no
  `*.secret` path in the index or the `HEAD` tree (those are plaintext in
  history; enabling v3 would only appear to protect them).
  Generate metadata, install Git filters, install the local `pre-commit`
  (`verify-index`) and `pre-push` (`audit` of the pushed commits) hooks and,
  where no foreign hook of that name exists, `post-checkout`, `post-merge`
  and `post-rewrite` (`hydrate --auto`), and
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
- `smudge`: authenticate including the Git-provided `%f` path; reject all
  other bytes. Release the plaintext only if the umask inherited from Git
  (which Git applies when it creates the worktree file, `0666 & ~umask`) has
  all group and other bits set; otherwise emit the authenticated record
  unchanged, so Git never writes plaintext readable by other users. The
  `post-checkout`, `post-merge` and `post-rewrite` hooks run
  `hydrate --auto` (a no-op while locked that never fails the finished Git
  command), which decrypts with mode 0600.
  The committed policy says `-diff` (no textconv, so no textconv cache). A
  local `diff=transcrypt-v3` (in `.git/info/attributes`) selects an external
  diff driver (`<bin> diff`). Git passes it the full path of each side. It
  authenticates each record side at that path (plaintext sides, i.e. the
  worktree, are shown as is), writes both plaintexts as exclusive 0600 files
  in the private scratch directory, runs `diff -u`, and removes them. While
  locked it prints only that the files differ.
- **Filter transport.** Git runs the filters through its long-running
  protocol (`filter.transcrypt-v3.process = <bin> filter-process`, protocol
  version 2): one process per Git command, advertising `clean` and `smudge`
  only. Each pkt-line length is decoded by the verified core
  (`decode_pkt_len`: four lowercase hex digits, flush or 5..65520 bytes);
  each file goes through exactly the per-file conversion; content beyond
  the 16 MiB bound is read to its flush and refused with `status=error`; a
  malformed packet ends the process, so Git fails the command. The per-file
  `clean %f` / `smudge %f` filters remain configured for Git versions
  without the protocol.
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
  one `git cat-file --batch` per process whose every reply must be exactly
  `<oid> blob <size>` LF, `<size>` bytes, LF (re-serialized and compared), never
  by `:<path>` revision syntax (which reads
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
  envelope. Commits are streamed from `rev-list` and each is checked for
  what it changes relative to its first parent (its whole tree for a root
  commit or a config change); a parent outside the selected range is trusted
  as already published. `--max-commits=N` bounds the work. Every Git
  subprocess's output is capped at 256 MiB (the process is killed beyond
  that) and its error output is drained and capped.
- `rekey`: requires the unlocked agent and that every protected file is
  exactly the plaintext of its staged record (after hydrating). A fresh
  salt and the new passphrase give a new config. Every staged record is
  re-encrypted under it; all records and the config are written as objects
  and staged in one `update-index -z --index-info`. Only then are the
  worktree config and the agent switched. Before the agent switch,
  `git reset` undoes it. Commits made before the rekey keep their records
  under the old config and passphrase.
- **Worktrees.** The repository's shared Git directory
  (`--git-common-dir`) holds the agent's session directory, the hooks and
  `info/`. Each worktree's own Git directory holds its private staging and
  scratch directories. The agent socket is bound and connected by its bare
  name from inside the checked session directory, so deep paths never exceed
  `sun_path`. `lock` first runs `flush` in every other existing worktree
  (each in its own process). If any of them refuses, the agent keeps
  running; otherwise `lock` flushes its own worktree and stops the agent.
  Without an agent, `lock` succeeds only when no plaintext is left.
- `uninstall`: `lock` if unlocked. Then refuse while any protected file
  holds anything but a v3 envelope, or an untracked `*.secret` exists.
  Remove `filter.transcrypt-v3.*`, the hooks v3 installed (if unchanged),
  its ignore rules and its private directories. The committed attributes
  and config stay; without the filter, Git would store a new `*.secret` as
  plaintext, which the command warns about.
- A new passphrase typed on a terminal (`init`, `rekey`) is asked for twice.
- **Merge driver.** `init`/`unlock` configure `merge.transcrypt-v3.driver =
  <bin> merge %O %A %B %P` and add `*.secret merge=transcrypt-v3` to
  `.git/info/attributes` (local; the committed policy is unchanged). Steps:
  - Require the unlocked agent.
  - Open ours and theirs at the path `%P`; both must authenticate. A base
    that does not open there (a rename) is replaced by an empty base.
  - Write the three plaintexts as exclusive mode-0600 files in
    `.git/transcrypt-v3-scratch` (a real 0700 directory; files of crashed
  processes are removed on next use), run
    `git merge-file -p`, then remove the files.
  - Store the result (conflict markers included) through clean, and exit
    non-zero on conflicts.

  During a merge, `hydrate` (and `status`) accept unmerged index entries:
  - with unmerged protected paths, the staged-record verification is
    replaced by the agent and effective-filter checks for every protected
    path;
  - an unmerged file is decrypted when it is an authentic record for its
    path (the driver's result).
- `doctor`: report, and exit non-zero unless all hold:
  - the effective `filter.transcrypt-v3.{clean,smudge,required}` are this
    binary's, and no `process` filter overrides them;
  - a new `*.secret` file would get the filter;
  - the staged index verifies;
  - the `pre-commit` and `pre-push` hooks are installed, and
    `core.hooksPath` is unset. As a heuristic backstop it also refuses commits containing
  well-known editor or merge copies of protected files (`*.secret~`,
  `*.secret.sw[pox]`, `*.secret.orig`, `.bak`, `.tmp`, `.rej`, `.save`,
  `*.secret#`), which hold plaintext; `init`/`unlock` add these patterns to
  `.git/info/exclude`.
- `hydrate`: authenticate **every staged protected object**, the staged
  metadata and the effective filter attributes first. Then, for every
  protected index entry, the worktree file is replaced by plaintext **only
  if it is exactly an authentic record for its path**: the staged record, or
  another record that authenticates there (a version restored or
  stash-popped while smudge emitted ciphertext). It is replaced by exactly
  the plaintext that record opens to. Every other file (unchanged or edited
  plaintext) is left untouched and only made private (mode `& 0700`), so no
  edit is ever overwritten; replacing a record by its plaintext loses
  nothing, since clean seals it back to the same record. Decisions for all
  files are made before any write; a protected symlink or unreadable file
  aborts the whole run.

  Plaintext is published through mode-0600 exclusive temporary files in the
  private staging directory `.git/transcrypt-v3-staging` (a real mode-0700
  directory, never the worktree, so a crash cannot leave plaintext where
  `git add` would commit it). They are renamed with `renameat` into the
  protected file's parent directory, which was resolved once with
  `O_NOFOLLOW` per component; stale staging files are deleted. A file is
  replaced only if its stamp (device, inode, size, mtime, ctime) still
  equals the one read when it was checked.

  Afterwards, re-index exactly the files that now hold the staged plaintext
  (never an edited or different version, which would stage it) with
  `git update-index -z --stdin`: raw paths, never pathspecs, and never
  `--add` (`git add -- <path>` would read a tracked `[a].secret` as a glob
  and stage an untracked `a.secret`). Then verify that the staged blob IDs
  and modes have not changed. `hydrate` and `lock` hold an exclusive lock on
  the staging directory for their whole run. A same-UID writer can still
  race the final stamp check and the rename; multi-file atomicity is not
  claimed.
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
