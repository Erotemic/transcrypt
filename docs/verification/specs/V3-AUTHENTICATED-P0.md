# Transcrypt v3 secure-first proof of concept: canonical byte contract

> **Scope note (2026-10-25, revised):** this document specifies the v3
> authenticated bytes and the lifecycle of the Rust implementation. The
> [product charter](../V3-PRODUCT-CHARTER.md) changes made after `d8436c6`
> are **not** wire-format changes:
> - protected files are selected by Git attributes instead of a `*.secret`
>   suffix (the path policy's accepted set grows; no record's bytes change);
> - the derived key is stored locally by default.
>
> Path binding and exact AAD remain mandatory until a separately versioned,
> reviewed protocol says otherwise.

**Status:** Proposed experimental v3 protocol. No compatibility with released
legacy formats or the earlier `TCRYPT3:` experiment. The Rust implementation
must be built/tested and independently reviewed before security-sensitive use.
This document is **independent of the Rust source** and is the intended
reference for a future Bash implementation and Lean refinement proofs.

## Scope

One context and one fixed crypto suite. Protected files are those Git's
attributes select. The actions are:
- setup: `init`, `protect`, `unprotect`, `unlock`, `lock`, `rekey`,
  `migrate`, `uninstall`;
- invoked by Git: `clean`, `smudge`, the pre-commit hook, `hydrate`, and the
  merge and diff drivers;
- checks: `verify-index`, `audit`;
- read-only: `status`, `doctor`, `help`.

There are no nested contexts, no GPG, no streaming of files larger than
16 MiB, and no implicit plaintext fallbacks.

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
names use `/` separators, are 1 to 4,096 bytes, and contain no NUL and no
empty, `.` or `..` component. They are also not **reserved**: no
`.transcrypt/…` path, no `.gitattributes` (in any directory) and no
top-level `.gitmodules`; Git and v3 must read those unencrypted. No Unicode
normalization, case folding, absolute paths or filesystem-based
canonicalization is performed: Git path bytes are the authoritative
identity. The credential agent rejects missing or noncanonical path input.

**Selection.** A path is protected exactly when Git's effective `filter`
attribute for it is `transcrypt-v3`. v3 obtains this from
`git check-attr -z --stdin filter`. It sends raw path bytes and parses each
answer record `path NUL filter NUL value NUL` with the verified core, which
requires the requested paths, in order, and nothing else. Which attribute
files are consulted depends on the check:
- `--cached` (staged files) for verification;
- the worktree's for files `git add` will clean;
- a temporary index holding a commit's own `.gitattributes` blobs for
  `audit`.

The committed macro
`[attr]transcrypt filter=transcrypt-rs diff=transcrypt-rs merge=transcrypt-v3 -text`
lets a rule read `PATTERN transcrypt`. Until this revision only `*.secret`
paths were valid. Every previously valid path is still valid, except
`.transcrypt/*.secret`, which no prototype repository is known to contain.

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

- `init [PATTERN…]`: requires an ordinary Git repository without
  `.transcrypt` and without a foreign `pre-commit` or `pre-push` hook. It:
  1. generates the config (passphrase asked twice on a terminal);
  2. writes `.transcrypt/config` and ensures the top-level `.gitattributes`
     defines the `transcrypt` macro, both through the symlink-refusing
     repository-file writer;
  3. installs the filters, merge and diff drivers and hooks: `pre-commit`,
     `pre-push`, `pre-merge-commit` (the read-only `verify-index`: a merge's
     index holds the other side's content, which is checked, never
     repaired), and `post-checkout`, `post-merge` and `post-rewrite`
     (`hydrate --auto`, used by the private mode);
  4. unlocks, stages the config and attributes, and runs `protect` for each
     pattern.

  A failure at any step rolls back everything `init` created.
- `protect PATTERN…` / `unprotect PATTERN…`: add or remove
  `PATTERN transcrypt` lines in the top-level `.gitattributes` (a pattern
  with blanks, quotes or control characters is C-quoted, as Git reads it)
  and stage it.
  - A pattern that would select `.gitattributes`, `.transcrypt/config` or
    `.gitmodules` is refused, and the edit is undone.
  - `protect` seals, in the index, every tracked file it newly selects whose
    staged blob is not a record. Their earlier commits stay plaintext; the
    command warns.
  - `unprotect` stages the authenticated plaintext of every file no longer
    selected, and lists them.
- `unlock [--private]`: derive from a terminal passphrase or opt-in stdin,
  and authenticate the config **first**.
  - **Default (stored key):** the 55-byte config it unlocks followed by the
    64-byte derived key, never the passphrase, is written to
    `$GIT_COMMON_DIR/transcrypt-v3/key`. This is a
    regular file, mode 0600, created exclusively and renamed into place in a
    mode-0700 directory owned by the user. It is not in `git config`.
    Every use reads it with `O_NOFOLLOW` and requires exactly 119 bytes.
    The key is used for the worktree config only if that config equals the
    stored one and authenticates with it; otherwise (a pulled `rekey`) the
    worktree counts as locked. Smudge may also open a record that names the
    stored config, which a checkout writes before `.transcrypt/config`.
  - **Private mode:** the key goes over a private one-way stdin pipe to a
    dedicated credential process that keeps it in memory. Its only
    persistent endpoint is a mode-`0600` Unix-domain socket at
    `.git/transcrypt-v3/session.sock`, beneath a mode-`0700` directory.
    Clients send operation, exact public config, canonical path bytes and
    data; the raw key is **never returned**. The agent authenticates the
    supplied config on every operation, and exits when it refuses a request
    while its worktree's config no longer equals its own (a pulled rekey).
    Stale sockets left by dead processes are reclaimed only after verifying
    the socket type and that it has no listening peer. An optional idle
    limit (`--timeout`), sent after the key over the same pipe, makes the
    agent exit, forgetting the key, after that long without a request.

  Each mode removes the other's credential. Both use the same verified
  core, so they produce byte-identical records.
- `clean`: require the Git-provided `%f` path as a single argument (refusing
  reserved paths with an explanation) and emit a complete path-bound
  authenticated record.
  - Clean is **idempotent**, as Git expects of filters: input that already
    opens as a record at this path under this config is returned unchanged
    (by determinism, exactly the record that sealing its plaintext gives).
  - A record of another configuration (cherry-picked or rebased across a
    rekey) passes through unchanged; verification refuses to commit it, and
    `reencrypt` re-seals it. Any other record of this configuration that
    does not open here is refused (no double encryption); everything else
    is sealed.
  - In private mode, clean also makes the worktree file private when it
    seals plaintext (`fchmod` through the symlink-refusing resolution); a
    failure fails the filter.
- `smudge`: the verified `smudge_action` decides.
  - Bytes without the v3 envelope are refused: plaintext committed without
    the filter is never presented as a protected file.
  - The key used is the one whose config the record names: the worktree's,
    or the stored key's own. The worktree config is re-read for every file.
  - A record of another configuration (history before a rekey), or any
    record while locked, is kept unchanged.
  - A record of this configuration is opened, authenticated at the `%f`
    path, or the filter fails (with instructions for a `git mv`d file).
  - In private mode the plaintext is released only if the umask inherited
    from Git (which Git applies when it creates the worktree file,
    `0666 & ~umask`) has all group and other bits set. Otherwise the
    authenticated record is emitted unchanged and the hooks or `hydrate`
    publish the plaintext with mode 0600.
- **Diff driver.** The macro's `diff=transcrypt-v3` selects an external
  driver (`<bin> diff`), to which Git passes the full path of each side.
  - It authenticates each record side at that path, and the new side of a
    staged rename also at the old path. Plaintext sides, i.e. the worktree,
    are shown as is.
  - It writes both plaintexts as exclusive 0600 files in the private scratch
    directory, runs `diff -u`, and removes them.
  - While locked it prints only that the files differ.
- **Filter transport.** Git runs the filters through its long-running
  protocol (`filter.transcrypt-v3.process = <bin> filter-process`, protocol
  version 2): one process per Git command, advertising `clean` and `smudge`
  only.
  - The config and key are loaded once per process.
  - Each pkt-line length is decoded by the verified core (`decode_pkt_len`:
    four lowercase hex digits, flush or 5..65520 bytes).
  - Each file goes through exactly the per-file conversion; content beyond
    the 16 MiB bound is read to its flush and refused with `status=error`.
  - A malformed packet ends the process, so Git fails the command.

  The per-file `clean %f` / `smudge %f` filters remain configured.
- **Locked clean.** Without a key for the worktree config, clean outputs
  input that has the v3 envelope of this config unchanged and refuses
  everything else, explaining whether the checkout is locked or its stored
  key is stale. A locked checkout behaves like a clone that never ran
  `unlock`, and plaintext can never be cleaned into the index.
- **Git object access.** Every staged or committed object is read by the
  object id from one `ls-files --stage -z` (or `ls-tree`/`diff-tree`)
  snapshot, through one `git cat-file --batch` per process.
  - Every reply must be exactly `<oid> blob <size>` LF, `<size>` bytes, LF
    (re-serialized and compared).
  - Objects are never read by `:<path>` revision syntax.
  - Object ids must be 40 or 64 lowercase hex digits.
  - Every Git subprocess runs with `GIT_LITERAL_PATHSPECS=1` and
    `GIT_NO_REPLACE_OBJECTS=1`.
  - Blob reads stop at the 16 MiB record bound.
- `verify-index` (read-only): the staged `.transcrypt/config` must equal the
  worktree config, and every staged protected entry must be:
  - a regular file (`100644` or `100755`; a selected symlink or submodule is
    refused, since Git stores those unfiltered) and not reserved;
  - with the key: a record that opens at its path;
  - while locked: a record with the envelope of this config whose blob is
    not also at another path in the index or `HEAD` (a moved or copied
    record).
- **Pre-commit hook.** With the key, it first seals what Git staged without
  the filter, then runs the `verify-index` check. Entries unchanged since
  `HEAD` get only its keyless checks there (they are already in history);
  `verify-index`, `hydrate`, `lock`, merge commits and the audit
  authenticate every entry.
  - A protected entry whose blob is not a record is sealed at its path.
  - A record that opens at a `HEAD` path no longer in the index (a `git mv`)
    is re-sealed for its new path.
  - Only local changes are touched: the staged blob must differ from
    `HEAD`'s at that path, and no merge, cherry-pick, revert or rebase may
    be in progress. Content that came from a commit is never re-sealed, so
    a hostile move is refused rather than laundered.
  - It warns when a local attribute file outside the repository mentions
    `filter`.
- `audit [<rev-list arguments>]`: for every selected commit (default
  `HEAD`), every file that the commit's own attributes protect must be a
  regular file whose blob has the v3 envelope of the `.transcrypt/config`
  committed in the same tree.
  - A commit with protected files but no config is refused.
  - Reserved paths are never protected.
  - A record that the commit removed from one path and added at another is
    refused (moved without re-encryption).
  - It needs no key, so it can run in CI or a server-side hook; when the
    stored key authenticates that config, each record is also opened at its
    path. A keyless audit cannot detect forged records that merely carry a
    valid envelope.
  - The commit's attributes come from a temporary index holding exactly its
    `.gitattributes` blobs (`git check-attr --cached` with `GIT_INDEX_FILE`),
    which works on every supported Git and in bare repositories.
  - Commits are streamed from `rev-list`. Each is checked for what it
    changes relative to its first parent, or its whole tree for a root
    commit or a change of the config or of any `.gitattributes`. A parent
    outside the selected range is trusted as already published.
  - `--max-commits=N` bounds the work. Every Git subprocess's output is
    capped at 256 MiB.
  - The `pre-push` hook audits the pushed commits not already on the
    remote's tracking branches.
- `rekey`: requires the key and that every protected file is exactly the
  plaintext of its staged record (after hydrating).
  1. A fresh salt and the new passphrase give a new config.
  2. Every staged record is re-encrypted under it, and all records and the
     config are staged in one `update-index -z --index-info`.
  3. Only then is the worktree config written, through the
     symlink-refusing repository-file writer (never a path-based write that
     could follow a committed symlink), and the credential switched in the
     same mode.

  Commits made before the rekey keep their records under the old config and
  passphrase.
- `migrate`: converts a checkout protected by Bash transcrypt (v2), whose
  filters have decrypted the worktree.
  1. Requires a committed worktree, and that no `filter=crypt[-ctx]` file
     still holds v2 ciphertext.
  2. Rewrites every tracked `.gitattributes` rule with
     `filter|diff|merge=crypt[-ctx]` tokens to the `transcrypt` macro, and
     sets aside Bash's own pre-commit hook.
  3. Runs `init`, re-cleans exactly the v2-protected files with
     `git add --renormalize`, and verifies the index with the key.

  Any failure restores the attribute files and hook and rolls back `init`.
  The v2 configuration and password are never removed by v3.
- **Worktrees.** The repository's shared Git directory
  (`--git-common-dir`) holds the stored key or the agent's socket, the
  hooks and `info/`. Each worktree's own Git directory holds its private
  staging and scratch directories. `lock` first runs `flush` in every other
  existing worktree; if any refuses, the key is kept. Otherwise `lock`
  flushes its own worktree and deletes the stored key or stops the agent.
  Without a key, `lock` succeeds only when no plaintext is left.
- `uninstall`: `lock` if unlocked. Then refuse while any protected file
  holds anything but a v3 envelope, or an untracked protected file exists.
  Remove `filter.transcrypt-v3.*` and the driver configuration, the hooks
  v3 installed (if unchanged), the key and its private directories. The
  committed attributes and config stay.
- **Merge driver.** The macro's `merge=transcrypt-v3` selects
  `<bin> merge %O %A %B %P`:
  - Require the key.
  - Open ours and theirs at the path `%P`; both must authenticate. A base
    that does not open there (a rename) is replaced by an empty base.
  - Write the three plaintexts as exclusive mode-0600 files in
    `.git/transcrypt-v3-scratch` (a real 0700 directory; files of crashed
    processes are removed on next use), run `git merge-file -p`, then
    remove the files.
  - Store the result (conflict markers included) through clean, and exit
    non-zero on conflicts.

  During a merge, `hydrate` and `status` accept unmerged index entries: an
  unmerged protected file is decrypted when it is an authentic record for
  its path (the driver's result).
- `doctor`: report, and exit non-zero unless all of these hold:
  - the effective filter, merge and diff driver settings are this binary's;
  - the protected-file selection is valid;
  - the staged index verifies;
  - the `pre-commit` and `pre-push` hooks are installed;
  - `core.hooksPath` is unset;
  - no local attribute file (`info/attributes`, `core.attributesFile`)
    mentions `filter`.
- `hydrate`: authenticate **every staged protected object** and the staged
  config first.
  - For every protected index entry, the worktree file is replaced by
    plaintext **only if it is exactly an authentic record for its path**:
    the staged record, or another record that authenticates there.
  - It is replaced by exactly the plaintext that record opens to. Every
    other file (unchanged or edited plaintext) is left untouched (in private
    mode, made private), so no edit is ever overwritten.
  - Decisions for all files are made before any write; a protected symlink
    or unreadable file aborts the whole run.

  Plaintext is published through exclusive temporary files in the private
  staging directory `.git/transcrypt-v3-staging` (a real mode-0700
  directory, never the worktree):
  - The new file keeps the replaced file's permission bits (an executable
    stays executable), restricted to the user in private mode.
  - It is renamed with `renameat` into the protected file's parent
    directory, which was resolved once with `O_NOFOLLOW` per component.
  - A file is replaced only if its stamp (device, inode, size, mtime,
    ctime) still equals the one read when it was checked.

  Afterwards, re-index exactly the files that now hold the staged plaintext
  with `git update-index -z --stdin` (raw paths, never pathspecs, never
  `--add`), then verify that the staged blob IDs and modes have not changed.
  `hydrate`, `lock`, `rekey`, `protect` and `unprotect` hold an exclusive
  lock on the staging directory while they write.
- `lock`: preflight no dirty or untracked protected files. Then:
  1. Overwrite tracked plaintext working files with the exact ciphertext in
     the index. This happens only when resealing the worktree reproduces
     that ciphertext byte for byte, through the same private staging
     directory, and only if the file's stamp is unchanged.
  2. Re-index those paths while the key is still available.
  3. Delete the stored key, or stop the agent.

  An interrupted `lock` is resumed by rerunning it. This is NOT certified
  secure deletion, atomic across multiple files, or protection against
  plaintext in caches, memory dumps, swap, snapshots, or backups.

Process and filesystem hardening:
- Every v3 process disables core dumps and, on Linux, is non-dumpable (no
  same-UID `ptrace` or `/proc/PID/mem` access); the agent `mlock`s its key
  page where permitted.
- Protected paths and v3-maintained repository files are resolved with
  `openat(O_NOFOLLOW)` per component and replaced with `renameat` relative
  to the held directory descriptors.
- The credential directory and socket must be owned by the effective UID,
  and both client and agent refuse a socket peer running as another UID.
- Argon2id runs in caller-supplied memory that is wiped afterwards, and
  AES-SIV encrypts and decrypts in place in caller buffers.

Remaining limits:
- The stored key and unlocked plaintext are readable by programs running as
  the same user (by design; see the charter), and the agent socket is
  usable by them.
- Same-UID processes can race on file *contents*.
- Multi-file operations are resumable rather than atomic.
- Files above 16 MiB are refused.
- Rollback of Git history is not detected.

## Machine checkability and implementation correspondence

- `rust/crates/transcrypt-v3-core/src/lib.rs`: pure `no_std` implementation
  of the encoders, strict parsers **and every protocol decision**: path
  policy, configuration authentication, record sealing (including refusing
  inputs that already are v3 records) and opening (zeroing the output on
  authentication failure), the smudge decision, agent request authorization,
  parsing of Git's attribute answers and the hydrate/lock actions. Cryptography enters only through the
  `V3Primitives` trait. Translated by Charon/Aeneas and proved against
  `proofs/lean/Transcrypt/V3Policy.lean`; see
  `proofs/aeneas/v3/PROOF-STATUS.md`.
- `rust/crates/transcrypt-rs/src/lib.rs`: KDF and AES-SIV adapter invoking
  external cryptographic libraries. Their algorithmic correctness and
  constant-time behavior are separate trusted assumptions.
- `rust/crates/transcrypt-rs/src/main.rs`: Git/OS adapter, to be tested under
  fault injection and eventually related to a transition specification.
- `tests/v3/reference/check_vectors.py`: independent Python reference using
  argon2-cffi and OpenSSL-backed `cryptography.AESSIV`; generates committed
  hex vectors in `vectors.tsv`, also consumed by Rust tests.
- `proofs/aeneas/translate-v3-core.sh`: reproducible translation entrypoint;
  the tracked extraction and its refinement proofs build in CI.

Bash correspondence: the released Bash 2.x script has **not** been changed
to support this format (`transcrypt-rs migrate` converts its repositories). They must implement exactly the same
ordered AAD and record grammar to become interoperable. Existing Bash
legacy behavior is not a requirement on this secure-first Rust implementation.

Correspondence and proof obligation map: [`v3-core-traceability.md`](../reference/v3-core-traceability.md).

## Private-mode agent framing (adapter-only, not part of the committed wire protocol)

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

In private mode only the live credential agent performs encryption and
decryption. It should not be confused with a verified enclave: same-UID processes can use the socket,
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
