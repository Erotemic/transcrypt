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
`pre-commit` or `pre-push` hook already exists. It leaves the repository
**unlocked**.

## Clone and unlock

```bash
git clone <url> my-repo && cd my-repo   # *.secret files arrive as ciphertext
transcrypt-v3 unlock
                                         # also decrypts the staged *.secret files
```

`unlock` authenticates the passphrase against the committed config **before**
changing anything. A wrong passphrase or a tampered config is rejected and no
key agent is started. It then hydrates: it authenticates every staged
protected file and replaces each ciphertext copy with its plaintext. If a
worktree file is neither the staged ciphertext nor its plaintext, hydration
refuses and changes nothing (unlock still succeeds and tells you); fix the
file and run `transcrypt-v3 hydrate`, which is safe to rerun after an
interruption. `unlock --no-hydrate` leaves ciphertext in place.

## Day to day

| Task | Command |
| --- | --- |
| See what is locked, decrypted or modified | `transcrypt-v3 status` |
| Edit and commit secrets | edit, `git add`, `git commit` (encryption is automatic) |
| Check the staged secrets before committing | `transcrypt-v3 verify-index` (also the pre-commit hook) |
| Check commits before pushing | `transcrypt-v3 audit origin/main..HEAD` (the pre-push hook does this) |
| Remove plaintext and forget the key | `transcrypt-v3 lock` |

`lock` refuses if any protected file has uncommitted or untracked changes, so
it never destroys the only copy of your data. Commit or discard the changes,
then lock again. If `lock` is interrupted, rerun it; files it already
replaced are recognized and skipped. A file you edit while `lock` or
`hydrate` runs is left alone and the command fails; rerun it.

While locked, the worktree holds ciphertext and Git keeps working:
`git status`, `git checkout`, `git pull` and commits of other files need no
key. Adding a plaintext `*.secret` fails until you unlock.

## Keep plaintext out of the remote

A `*.secret` file only gets encrypted in a checkout where `transcrypt-v3
unlock` (or `init`) installed the filters. In a fresh clone that never ran
`unlock`, `git add new.secret` stores **plaintext**, and no hook runs there.
Two checks catch this:

- The `pre-push` hook installed by `init`/`unlock` audits every commit you
  push, including merges, rebases and `--no-verify` commits that skipped the
  pre-commit hook.
- `transcrypt-v3 audit <rev-list arguments>` needs no key. Run it in CI or a
  server-side hook (for example `transcrypt-v3 audit origin/main..HEAD` on
  each pull request) to refuse plaintext from any checkout. Without the key
  it checks that each secret is a v3 record for the committed config; when
  unlocked it also authenticates every record.

For example, in GitHub Actions (any CI with Git ≥ 2.36 works the same way):

```yaml
- uses: actions/checkout@v4
  with: { fetch-depth: 0 }
- run: cargo install --locked --path rust/crates/transcrypt-v3   # or a released binary
- run: transcrypt-v3 audit --all     # every commit on every branch; no key needed
```

On a self-hosted server, a `pre-receive` hook can run
`transcrypt-v3 audit <new> --not --all` for each updated ref.

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
- **Hooks are local.** `git push --no-verify`, a clone that never ran
  `unlock`, or a server without `transcrypt-v3 audit` is not checked. The
  clean filter still encrypts everything it processes. If `core.hooksPath`
  is set, Git ignores `.git/hooks`; `status` warns about this.
- **Use `umask 077` in protected checkouts.** `hydrate` writes plaintext
  with mode 0600, but files Git writes on checkout (through the smudge
  filter) and files you create get your umask, often readable by other
  local users. `transcrypt-v3 status` warns about such files.
- Files larger than 16 MiB are refused.

## Troubleshooting

| Message | Meaning and fix |
| --- | --- |
| `v3 session is locked; run unlock` | No live key agent: `transcrypt-v3 unlock` |
| `refusing double encryption` | You tried to add a file that is already a v3 record; restore the plaintext instead |
| `protected worktree differs from staged ciphertext and its plaintext` | A file has local edits the tool did not expect; inspect with `status`, then commit or restore it |
| `required effective transcrypt-v3 filter` | Some attributes file (for example `.git/info/attributes` or a nested `.gitattributes`) disables the filter for a `*.secret` path; remove that override |
| `unsafe .git/transcrypt-v3...` | A credential or staging path is a symlink, has loose permissions or belongs to another user; remove it and unlock again |
| `another transcrypt-v3 hydrate or lock is running` | Wait for it to finish |
| `protected worktree file changed after it was checked` | Something wrote the file during `lock`/`hydrate`; rerun the command |
| `refusing to push` / `not v3 ciphertext for its configuration (plaintext?)` | A commit contains an unencrypted secret: rewrite it out of the unpushed history (for example `git rebase -i`), and rotate the secret if it was ever pushed |

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
