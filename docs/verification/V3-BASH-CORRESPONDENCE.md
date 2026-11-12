# Transcrypt (Bash) ↔ transcrypt-rs (Rust): correspondence

This maps the shipped Bash `transcrypt` (the v2 protocol) onto the Rust
`transcrypt-rs` command and protocol, so that a Bash user knows what each
command becomes, and a reviewer can see exactly which mechanism replaces
which. v3 is a *new protocol*, not a re-implementation of v2: the two cannot
read each other's ciphertext. The bridge from Bash **v2** to v3 is an
explicit one-time `migrate` (in either v3 client), not legacy binary
compatibility. The tables below map v2 commands onto the v3 commands; the
portable v3 client `contrib/v3/transcrypt-bash` has the same command names
and behavior as `transcrypt-rs` for profiles 2 and 3
([guide](../../contrib/v3/README-BASH.md),
[spec](specs/V3-PORTABLE-PROFILES.md)).


## Commands

| Bash `transcrypt` | `transcrypt-rs` | Notes |
| --- | --- | --- |
| `transcrypt` (interactive setup), `-c CIPHER -p PASSWORD -y` | `init` (`--password-stdin` for scripts) | **Current Rust P1** has one fixed suite, Argon2id/AES-SIV. Rust avoids passphrases in argv and requires at least 16 bytes; future portable Bash may expose passphrases/derived keys locally through OpenSSL CLI arguments. |
| setup in a fresh clone (`transcrypt -c … -p …`) | `unlock` | Authenticates the passphrase against the committed config *before* changing anything, stores the derived key (not the passphrase) in `.git/transcrypt-v3/key`, and decrypts. Like Bash, once per clone. `--private` keeps the key in memory only. |
| `-f`, `--flush-credentials` | `lock` | Bash force-checks-out the encrypted files (a clean tree is required unless `--force`, which discards changes). v3 refuses while any protected file has uncommitted changes and never discards plaintext it cannot restore; then it deletes the stored key. |
| `-d`, `--display` | `status` | v3 never displays the passphrase (it is not stored anywhere). |
| `-l`, `--list`, `git ls-crypt` | `status` | Also shows each file's state and untracked protected files. |
| `-s FILE`, `--show-raw` | `git show HEAD:FILE` | Every committed protected blob is a v3 record. |
| pre-commit hook (checks the `Salted` prefix; since F-01 also decryption and salt) | pre-commit hook (`pre-commit`) | v3 encrypts protected files staged around the filter, re-encrypts `git mv` renames, then authenticates every staged record at its path. |
| — | pre-push hook, `audit`, `contrib/v3/pre-receive` | No Bash equivalent: keyless refusal of plaintext in pushed history. |
| — | `doctor`, `contrib/v3/check-remote-enforcement` | No Bash equivalent. |
| `--add PATTERN`, editing `.gitattributes` (`filter=crypt diff=crypt merge=crypt`) | `protect PATTERN`, or `PATTERN transcrypt` in `.gitattributes` | Same selection model: Git's attributes. `transcrypt` is a macro for `filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text`. `unprotect` reverses it. |
| `-C`, `--context`, `--list-contexts` | — | v3 has one passphrase per repository. |
| `-r`, `--rekey` | `rekey` | A new config (fresh salt) and every secret re-encrypted, staged as one change to commit. Refuses uncommitted edits. History stays readable with the old passphrase, as with Bash. |
| `-u`, `--uninstall` | `uninstall` | Locks first and leaves **ciphertext** (Bash leaves plaintext); removes only the filters, hooks and key v3 installed. |
| — | `migrate` | One-time conversion of a Bash-protected checkout: keeps the patterns, re-encrypts the decrypted files with v3. |
| `-e` / `-i` (`--export-gpg` / `--import-gpg`) | — | Share the passphrase out of band. |
| `--upgrade`, `--set-openssl-path` | — | One self-contained binary; no OpenSSL. |

## Mechanisms

| Concern | Bash (v2) | transcrypt-rs |
| --- | --- | --- |
| Encryption | OpenSSL `enc -aes-256-cbc` (configurable), base64 | AES-256-SIV (RFC 5297), binary, 16-byte synthetic IV/tag |
| Authentication | None: modified or swapped ciphertext decrypts to garbage, or to another file's plaintext | Every record is authenticated; a record moved to another path, repository config or key does not open |
| Key derivation | `EVP_BytesToKey` with MD5, one iteration | Argon2id, m = 64 MiB, t = 3, p = 1, 32-byte random salt |
| Determinism (needed by Git) | Per-file salt = HMAC-SHA256(file name + password), truncated | SIV is deterministic; associated data = `[domain, config, exact Git path]` |
| Where the secret lives | Password in plaintext in `.git/config` (`transcrypt.password`) | The Argon2id-derived key (never the passphrase) in `.git/transcrypt-v3/key`, mode 0600, outside `git config`, until `lock`. Optional private mode: in memory only (a non-dumpable agent behind a 0600 socket) |
| Selection | `.gitattributes` patterns with `filter=crypt` (or `crypt-<context>`) | `.gitattributes` patterns with `filter=transcrypt-v3` (the `transcrypt` macro); parsed answers from `git check-attr`, never a second glob engine |
| Public metadata | Cipher in `.git/config` (local, not committed) | `.transcrypt/config` (committed, authenticated by the key) |
| Git integration | `filter=crypt diff=crypt merge=crypt`, textconv with `cachetextconv` (plaintext in `refs/notes/textconv`) | `filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text` via the committed `transcrypt` macro; drivers configured locally. No textconv cache. |
| Renames | Path-independent CBC ciphertext moves freely (and so can be swapped between files undetected) | Records are path-bound; the pre-commit hook re-encrypts `git mv` renames; a keyless audit refuses unbound moves |
| Diffs | textconv with `cachetextconv`: plaintext cached in `refs/notes/textconv` | External diff driver: each side authenticated at its path, no cache |
| Merging | `merge=crypt` driver: decrypt, `git merge-file`, re-encrypt | Same idea: authenticated decryption of all three versions, merged in a private 0700 directory, the result re-encrypted |
| Filter process | One Bash process per file | Git's long-running filter protocol: one process per Git command |
| Plaintext permissions | Git's umask | Git's umask by default; private mode never lets plaintext be readable by others (`umask`-aware smudge, 0600 hydration) |
| Failure behavior | A failed decryption silently passes the input through (`git_smudge` falls back to the raw bytes) | Fail closed: a record of this config that does not authenticate fails the Git command; bytes that are no record are refused; only another config's record (old history) is left encrypted |
| Verification | Shell tests | Verified Rust core (Charon/Aeneas → Lean, independent spec), real-Git adversarial tests, differential crypto tests ([V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md)) |

## Moving a repository from Bash to v3

`transcrypt-rs migrate`, run in a checkout where Bash transcrypt has
decrypted the files (details in the [user guide](V3-USER-GUIDE.md#moving-from-bash-transcrypt-v2)):

1. Refuses unless the worktree is committed and every `filter=crypt` file
   holds plaintext.
2. Rewrites each `filter=crypt[-ctx] diff=… merge=…` rule to the
   `transcrypt` macro (same patterns, nested files included), and sets
   aside Bash's pre-commit hook.
3. Initializes v3 (new passphrase) and re-encrypts those files from the
   worktree plaintext; verifies the staged index with the key.
4. Rolls everything back on any failure; never modifies the plaintext and
   never deletes the v2 configuration or password.

The user commits, checks that a fresh clone unlocks, then removes the v2
credentials. The old history keeps the v2 ciphertext, protected only by the
Bash password (now also fixed for review F-01): rotate those secrets if the
history or password was exposed. The v3 binary contains no v2 cryptography.

## Bash v3 ↔ Rust v3 compatibility

Achieved for profiles 2 (scrypt) and 3 (PBKDF2): both clients write
byte-identical configs, records and stored key files, inspect the committed
profile before changing anything, refuse unsupported profiles by name, and
can alternate on one repository (and in one checkout). Profile 1 (Argon2id)
is Rust-only; the Bash client reports it and changes nothing. Rust-only by
design: `--private`, `reencrypt`, the long-running filter and in-process key
handling. Evidence: `tests/v3/bash/test_reference.sh` and the two-way
`tests/v3/conformance/run.sh`; the per-workflow matrix is in the
[dual-implementation roadmap](V3-DUAL-IMPLEMENTATION-ROADMAP.md). Proofs
about Rust do not prove the Bash source (A27).

## Formal correspondence

The spec-level correspondence for the Bash code (function-by-function
review records) is the method of
[09-bash-traceability-and-review](09-bash-traceability-and-review.md). For
v3, the independent wire specification and the Lean specification
in `proofs/lean/Transcrypt/` constrain the Rust implementation and provide
a shared target for empirical Bash conformance; on a common profile, the
Bash and Rust outputs must match byte for byte. The independent
vectors in `tests/v3/reference/` are the conformance tests it must pass.

The decisions behind interrupted commands and the pre-push verdict are
verified core functions in Rust; `transcrypt-bash` reimplements each one
line for line, and the two clients' suites and the lifecycle campaign test
that they agree (assumption A27; no theorem covers the Bash source):

| Verified core (`transcrypt-v3-core`) | `transcrypt-bash` |
| --- | --- |
| `setup_record_use` | `tc_record_use` (fresh, merge, other, unrecorded) |
| `entry_recovery` | `tc_rekey_resume`: `case ${now[$path]}` (mode and want: done; mode and other: todo; else changed) |
| `config_recovery` | `tc_rekey_resume`: the `cmp -s` of the worktree config against both configs |
| `file_recovery` | `tc_rekey_resume`: relock on `cmp` with the replaced record, keep on the wanted one, else the plaintext check |
| `push_admission` | `tc_cmd_pre_push`: refuse when keyless records needed the key (`TC_AUDIT_NEEDS_KEY`) and authenticated pushes are required, else warn |
| `authenticated_push_required` | `tc_push_required`: required unless `transcrypt.requireAuthenticatedPush` is set and `git config --bool` reads it as `false` |
| `admission_selected` | `tc_selected` with `--cached`: a path is selected when Git's effective answer or the isolated policy answer (`tc_policy_git`) selects it |

## Legacy review, retained security guarantees and migration boundary

The [independent October 2026 assessment]
(reviews/2026-10-25-independent-source-assessment.md) reproduced a Bash v2
plaintext-staging bypass involving the `U2FsdGVk` prefix (F-01). It is fixed
in the Bash script: input counts as ciphertext only if it decrypts under the
repository key and embeds the deterministic per-path salt. v2 remains
unauthenticated CBC. Existing installs must run `transcrypt --upgrade` to
replace the hook's helper copy, and history from before the fix should be
audited. None of this adds legacy CBC/MD5 to the formally verified v3
runtime; a v3 transition is explicit and cannot retroactively authenticate
older public history. See [V3-REVIEW-TRIAGE](V3-REVIEW-TRIAGE.md).
