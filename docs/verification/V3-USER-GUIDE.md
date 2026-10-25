# Transcrypt v3 user guide (experimental Rust)

`transcrypt-v3` encrypts every Git-tracked file whose name ends in `.secret`.
Encryption happens in Git's clean filter, so the repository, its history and
every remote only ever contain authenticated ciphertext. Your worktree holds
plaintext while the repository is unlocked.

> **Status.** Experimental. The protocol core is machine-checked against an
> independent specification (see [what is proved](#what-is-and-is-not-proved)),
> but the implementation has not had an independent security review. Do not
> use it as your only protection for high-value secrets.

## Install

```bash
cd transcrypt/rust
cargo build --release -p transcrypt-v3
# put target/release/transcrypt-v3 on your PATH; Git filters record its absolute path
```

Requirements: Unix (Linux or macOS), Git, and a normal checkout with a `.git`
directory. Linked worktrees and submodules are not supported yet.

## Start protecting a repository

```bash
cd my-repo
transcrypt-v3 init                 # choose a passphrase of at least 16 bytes
git commit -m "Enable transcrypt v3" .transcrypt/config .gitattributes
echo "api-token" > deploy/token.secret
git add deploy/token.secret        # encrypted by the clean filter
git commit -m "Add token"
```

`init` refuses to run if `.transcrypt/`, `.gitattributes` or a foreign
pre-commit hook already exists. It leaves the repository **unlocked**.

## Clone and unlock

```bash
git clone <url> my-repo && cd my-repo   # *.secret files arrive as ciphertext
transcrypt-v3 unlock
transcrypt-v3 hydrate                    # decrypt staged *.secret files into the worktree
```

`unlock` authenticates the passphrase against the committed config **before**
changing anything. A wrong passphrase or a tampered config is rejected and no
key agent is started. `hydrate` first authenticates every staged protected
file, then replaces each ciphertext copy with its plaintext. If a worktree
file is neither the staged ciphertext nor its plaintext, `hydrate` refuses
and changes nothing. It is safe to rerun after an interruption.

## Day to day

| Task | Command |
| --- | --- |
| See what is locked, decrypted or modified | `transcrypt-v3 status` |
| Edit and commit secrets | edit, `git add`, `git commit` (encryption is automatic) |
| Check the staged secrets before pushing | `transcrypt-v3 verify-index` (also the pre-commit hook) |
| Remove plaintext and forget the key | `transcrypt-v3 lock` |

`lock` refuses if any protected file has uncommitted or untracked changes, so
it never destroys the only copy of your data. Commit or discard the changes,
then lock again. If `lock` is interrupted, rerun it; files it already
replaced are recognized and skipped.

For scripts, `init` and `unlock` accept `--password-stdin`.

## What to expect

- **Renames re-encrypt.** Each ciphertext is bound to its exact Git path, so a
  record moved to another path does not decrypt. `git mv` re-runs the clean
  filter and works normally.
- **Equal plaintexts leak equality** at the same path in the same repository
  (deterministic encryption keeps Git diffs and merges stable).
- **Git diffs of `*.secret` files are disabled.** No plaintext is cached by
  textconv.
- **Rollback is not detected.** Someone who controls your Git history can
  restore an older valid version of a secret.
- **The key lives in a local agent process** reachable through a mode-0600
  socket in `.git/transcrypt-v3/`. Other programs running as your Unix user
  can use it while the repository is unlocked. The key is never written to
  disk.
- **Hooks are local.** A `--no-verify` commit or a server without the hook
  is not checked. The clean filter still encrypts everything it processes.
- Files larger than 16 MiB are refused.

## Troubleshooting

| Message | Meaning and fix |
| --- | --- |
| `v3 session is locked; run unlock` | No live key agent: `transcrypt-v3 unlock` |
| `refusing double encryption` | You tried to add a file that is already a v3 record; restore the plaintext instead |
| `protected worktree differs from staged ciphertext and its plaintext` | A file has local edits the tool did not expect; inspect with `status`, then commit or restore it |
| `required effective transcrypt-v3 filter` | Some attributes file (for example `.git/info/attributes` or a nested `.gitattributes`) disables the filter for a `*.secret` path; remove that override |
| `unsafe .git/transcrypt-v3...` | A credential or staging path is a symlink or has loose permissions; remove it and unlock again |

## What is and is not proved

The pure Rust protocol core (`rust/crates/transcrypt-v3-core`) is translated
to Lean by Charon/Aeneas and proved against an independent specification:
- the exact on-disk formats;
- the canonical-path policy;
- that plaintext is released only for a record authenticated under the
  repository config and its exact path;
- that `lock` never discards unrecoverable plaintext and `hydrate` only
  replaces exact staged ciphertext;
- that `verify-index` passing means every staged secret authentically opens.

These guarantees assume the cryptographic primitives behave as AES-SIV,
Argon2id and SHA-256, and that the Git/OS adapter follows the modeled steps.
See [V3-ASSUMPTIONS.md](V3-ASSUMPTIONS.md) for the exact, trust-ordered list
and [V3-PROOF-COVERAGE.md](V3-PROOF-COVERAGE.md) for theorem names.
