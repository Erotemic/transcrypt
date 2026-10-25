# Transcrypt (Bash) ↔ transcrypt-v3 (Rust): correspondence

This maps the shipped Bash `transcrypt` (the v2 protocol) onto the Rust
`transcrypt-v3` command and protocol, so that a Bash user knows what each
command becomes, and a reviewer can see exactly which mechanism replaces
which. v3 is a *new protocol*, not a re-implementation of v2: the two cannot
read each other's ciphertext. A future Bash implementation of v3 is optional and independently reviewed;
it must conform to the v3 byte spec if attempted. **One-time migration** from
Bash v2 to v3 is the near-term priority, not binary compatibility. The
[product charter](V3-PRODUCT-CHARTER.md) defines the future Rust defaults;
this table describes the current `861975a` implementation only.

## Commands

| Bash `transcrypt` | `transcrypt-v3` | Notes |
| --- | --- | --- |
| `transcrypt` (interactive setup), `-c CIPHER -p PASSWORD -y` | `init` (`--password-stdin` for scripts) | v3 has one fixed suite. The passphrase is never on the command line (argv is visible to other users) and must be at least 16 bytes. |
| setup in a fresh clone (`transcrypt -c … -p …`) | `unlock` | Authenticates the passphrase against the committed config *before* changing anything, then decrypts with mode 0600. |
| `-f`, `--flush-credentials` | `lock` | Bash force-checks-out the encrypted files (a clean tree is required unless `--force`, which discards changes). v3 refuses while any secret has uncommitted changes and never discards plaintext it cannot restore. Stops the key agent. |
| `-d`, `--display` | `status` | Current v3 does not save a credential. **Planned default:** persist a repository-scoped derived key locally (never in committed config), retaining session-only mode as an option. |
| `-l`, `--list`, `git ls-crypt` | `status` | Also shows each file's state, permissions and untracked secrets. |
| `-s FILE`, `--show-raw` | `git show HEAD:FILE` | Every committed `*.secret` blob is a v3 record. |
| pre-commit hook (checks the `Salted` prefix) | pre-commit hook (`verify-index`) | v3 authenticates every staged record at its path and checks Git's effective filter attribute. |
| — | pre-push hook, `audit`, `contrib/v3/pre-receive` | No Bash equivalent: keyless refusal of plaintext in pushed history. |
| — | `doctor`, `contrib/v3/check-remote-enforcement` | No Bash equivalent. |
| `--add PATTERN` | **Planned** `protect PATTERN` or direct `.gitattributes` | **Top priority:** let Git select arbitrary files; current v3 only uses `*.secret`, and its source-derived proof reflects that limitation. |
| `-C`, `--context`, `--list-contexts` | — | v3 has one passphrase per repository. |
| `-r`, `--rekey` | `rekey` | A new config (fresh salt) and every secret re-encrypted, staged as one change to commit. Refuses uncommitted edits. History stays readable with the old passphrase, as with Bash. |
| `-u`, `--uninstall` | `uninstall` | Locks first and leaves **ciphertext** (Bash leaves plaintext); removes only the filters, hooks and ignore rules v3 installed. |
| `-e` / `-i` (`--export-gpg` / `--import-gpg`) | — | Share the passphrase out of band. |
| `--upgrade`, `--set-openssl-path` | — | One self-contained binary; no OpenSSL. |

## Mechanisms

| Concern | Bash (v2) | transcrypt-v3 |
| --- | --- | --- |
| Encryption | OpenSSL `enc -aes-256-cbc` (configurable), base64 | AES-256-SIV (RFC 5297), binary, 16-byte synthetic IV/tag |
| Authentication | None: modified or swapped ciphertext decrypts to garbage, or to another file's plaintext | Every record is authenticated; a record moved to another path, repository config or key does not open |
| Key derivation | `EVP_BytesToKey` with MD5, one iteration | Argon2id, m = 64 MiB, t = 3, p = 1, 32-byte random salt |
| Determinism (needed by Git) | Per-file salt = HMAC-SHA256(file name + password), truncated | SIV is deterministic; associated data = `[domain, config, exact Git path]` |
| Where the secret lives | Password in plaintext in `.git/config` (`transcrypt.password`) | Nowhere on disk: a derived key in a memory-only agent (0600 socket in a 0700 directory, non-dumpable) until `lock` |
| Public metadata | Cipher in `.git/config` (local, not committed) | `.transcrypt/config` (committed, authenticated by the key) |
| Git integration | `filter=crypt diff=crypt merge=crypt`, textconv with `cachetextconv` (plaintext in `refs/notes/textconv`) | `filter=transcrypt-v3 -diff` committed; `diff=transcrypt-v3 merge=transcrypt-v3` set locally (`.git/info/attributes`). No textconv cache. |
| Diffs | textconv with `cachetextconv`: plaintext cached in `refs/notes/textconv` | External diff driver: each side authenticated at its path, no cache |
| Merging | `merge=crypt` driver: decrypt, `git merge-file`, re-encrypt | Same idea: authenticated decryption of all three versions, merged in a private 0700 directory, the result re-encrypted |
| Filter process | One Bash process per file | Git's long-running filter protocol: one process per Git command |
| Plaintext permissions | Git's umask (often world-readable) | Never readable by others when written by Git or transcrypt (`umask`-aware smudge and 0600 hydration) |
| Failure behavior | A failed decryption silently passes the input through (`git_smudge` falls back to the raw bytes) | Fail closed: a required filter fails the Git command; nothing unauthenticated is released |
| Verification | Shell tests | Verified Rust core (Charon/Aeneas → Lean, independent spec), real-Git adversarial tests, differential crypto tests ([V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md)) |

## Moving a repository from Bash to v3

**Product target:** ship a tested, explicit one-time migration that preserves
*arbitrary protected-file patterns* and recoverable plaintext. The steps
below are a **manual workaround for the current `*.secret` prototype**, not
the target migration experience or a promise that old history is secured.


v3 cannot decrypt v2 ciphertext, and `init` refuses a repository that
already tracks `*.secret` files (they are plaintext or v2 ciphertext in
history). Steps:

1. With Bash, decrypt the working copy (`transcrypt -u` leaves files
   decrypted).
2. **Current limitation:** rename protected files to `*.secret`, or move
   them into a fresh repository. The planned v3 selection support removes
   this forced rename.
3. Run `transcrypt-v3 init` and commit.

The old history keeps the v2 ciphertext, protected only by the Bash
password: rotate those secrets.

## Formal correspondence

The spec-level correspondence for the Bash code (function-by-function
review records) is the method of
[09-bash-traceability-and-review](09-bash-traceability-and-review.md). For
v3, the Lean specification in `proofs/lean/Transcrypt/` is the reference that
any future Bash v3 implementation must match byte for byte. The independent
vectors in `tests/v3/reference/` are the conformance tests it must pass.

## Legacy review, retained security guarantees and migration boundary

The [independent October 2026 assessment]
(reviews/2026-10-25-independent-source-assessment.md) reproduced a Bash v2
plaintext-staging bypass involving the `U2FsdGVk` prefix. That is a real
legacy risk and should inform maintained-v2 remediation, history inspection
and migration warnings. It does **not** justify adding legacy CBC/MD5 to the
formally verified v3 runtime. A v3 transition must be explicit and cannot
retroactively authenticate older public history. Review all changes using
[V3-REVIEW-TRIAGE](V3-REVIEW-TRIAGE.md).
