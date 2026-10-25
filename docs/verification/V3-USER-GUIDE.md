# Transcrypt v3 user guide (experimental Rust)

`transcrypt-v3` encrypts the files **you choose** in a Git repository. You
select them with ordinary `.gitattributes` patterns (`.env`,
`config/production.yaml`, `private/**`, `*.key`). Git stores those files
as authenticated ciphertext, so the repository and its history can be
public. Your unlocked checkout holds ordinary plaintext, and Git works as
usual.

What it protects, and what it does not (see the
[product charter](V3-PRODUCT-CHARTER.md)):

- **Protected:** the committed contents of selected files, against anyone
  who can read the repository but not the passphrase. A tampered,
  truncated, swapped or moved record is never decrypted to the wrong
  plaintext.
- **Not protected:**
  - Files you did not select.
  - Plaintext that was committed before you selected it (history keeps it).
  - Clones that never ran `unlock` (their `git add` stores plaintext; see
    [Keep plaintext out of the remote](#keep-plaintext-out-of-the-remote)).
  - Your unlocked workstation: anyone who can read your files or run
    programs as you can read the plaintext and the key, as with any
    unlocked checkout.
- **Public by design:** filenames, file sizes, commit structure, and
  whether two versions of a file at the same path are equal.

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

Requirements: Unix (Linux or macOS) and Git 2.34 or newer.

## Start protecting a repository

```bash
cd my-repo
transcrypt-v3 init .env 'secrets/**'   # choose a passphrase (16+ bytes, asked twice)
git commit -m "Enable transcrypt v3"
```

`init`:
- creates the public `.transcrypt/config`;
- adds the `transcrypt` attribute macro to `.gitattributes`, plus a
  `PATTERN transcrypt` line for each pattern;
- installs the filters and hooks;
- unlocks this checkout.

From then on, `git add` encrypts every selected file. Files that were
already tracked are encrypted in the index right away. `init` warns that
their earlier commits still hold plaintext, so change those secrets if that
history is public.

Choose more files at any time:

```bash
transcrypt-v3 protect config/production.yaml '*.pem'
git commit -m "Protect production config"
```

or edit `.gitattributes` yourself. These two lines are equivalent:

```gitattributes
config/production.yaml transcrypt
config/production.yaml filter=transcrypt-v3 diff=transcrypt-v3 merge=transcrypt-v3 -text
```

A file is protected exactly when Git's effective `filter` attribute for it
is `transcrypt-v3`. All of Git's rules apply: patterns, nested
`.gitattributes` files, later lines overriding earlier ones, and exclusions
such as `private/README.md -filter -diff -merge`. Quote a pattern containing
spaces: `"name with space.txt" transcrypt` (`protect` does it for you). Any
valid path works, including non-UTF-8 names and executable files.
`.gitattributes`, `.gitmodules` and `.transcrypt/` are never encrypted, since
Git and v3 must read them; `protect` refuses a pattern that would select
them.

`transcrypt-v3 unprotect PATTERN` removes a `PATTERN transcrypt` line and
stages the selected files' **plaintext**. Their next commit publishes them
unencrypted, which is the point; the command lists them.

## Clone and unlock

```bash
git clone <url> my-repo && cd my-repo   # protected files arrive as ciphertext
transcrypt-v3 unlock                     # once per clone
```

`unlock` checks the passphrase against the committed config **before**
changing anything; a wrong passphrase or a tampered config is rejected. It
then stores the derived key, decrypts the checkout, and you are done. Git
commands work without prompting, in new shells and after a reboot, with no
background process:
- checkout, switch, pull, merge, rebase, stash, restore;
- diff and log (`git log -p --ext-diff` shows decrypted diffs);
- worktrees.

If decryption cannot run (for example, a protected file is a symlink), it
changes nothing; unlock still succeeds and tells you why. Fix the cause and
run `transcrypt-v3 hydrate`, which is safe to rerun at any time.
`unlock --no-hydrate` leaves the ciphertext in place.

**Where the key is.** The key is derived from your passphrase by Argon2id;
the passphrase itself is stored nowhere. The key is in
`.git/transcrypt-v3/key` (mode 0600, in a 0700 directory, shared by all
worktrees of the clone). It is not in `.git/config`, so `git config --list`
does not show it. But anything that copies `.git` (a backup, a tarball, a
support bundle) copies the key. Whoever has it can decrypt this repository's
history, just as whoever can read your unlocked checkout can read its files.
`transcrypt-v3 lock` deletes it.

**Private mode (optional).** `transcrypt-v3 unlock --private` keeps the key
only in the memory of a small background agent until `lock` or logout,
never on disk. It also keeps decrypted files private to you (mode 0600):
- Git writes plaintext only when your umask is private.
- Otherwise the post-checkout, post-merge and post-rewrite hooks decrypt
  with mode 0600 right after Git finishes.
- After `git restore`, `git reset --hard` or `git stash pop` (no hook runs),
  run `transcrypt-v3 hydrate`.

Other programs running as your user can still use the agent while you are
unlocked. `unlock --private --timeout=15m` (or `90s`, `2h`) also makes the
agent forget the key after that long without use. Decrypted files stay
until you `lock`; Git then treats the checkout as locked. Both modes produce byte-identical ciphertext; switch with `unlock`
or `unlock --private`.

## Day to day

| Task | Command |
| --- | --- |
| See what is protected, locked, decrypted or modified | `transcrypt-v3 status` |
| Check that this checkout is protected | `transcrypt-v3 doctor` (non-zero exit if something is missing) |
| Check that a remote refuses plaintext | `contrib/v3/check-remote-enforcement origin` |
| Edit, stage and commit protected files | as usual: `git add`, `git commit` |
| Rename or move one | `git mv` as usual (see below) |
| Check the staged files without committing | `transcrypt-v3 verify-index` |
| Check commits before pushing | `transcrypt-v3 audit origin/main..HEAD` (the pre-push hook does this) |
| Remove plaintext and forget the key | `transcrypt-v3 lock` (safe to repeat; so is `unlock`) |
| Change the passphrase | `transcrypt-v3 rekey`, then commit the staged change |
| Remove v3 from this checkout | `transcrypt-v3 uninstall` (locks first; files stay encrypted) |

**Renames.** Each record is bound to its path, and `git mv` keeps the old
record. When you commit, the pre-commit hook re-encrypts a renamed file for
its new path (directories too), and encrypts a file moved in from an
unprotected name. To make `git diff --cached` show the change before
committing, `git add` the new path. While locked, a renamed protected file
cannot be re-encrypted, so the commit is refused until you unlock.

`lock` refuses if any protected file has uncommitted or untracked changes,
so it never destroys the only copy of your data. Commit or discard the
changes, then lock again. If `lock` is interrupted, rerun it; files it
already replaced are recognized and skipped. A file you edit while `lock` or
`hydrate` runs is left alone and the command fails; rerun it.

While locked, the worktree holds ciphertext and Git keeps working:
`git status`, `git checkout`, `git pull` and commits of other files need no
key. Adding a plaintext protected file fails until you unlock.

**After someone else rekeys.** Once you pull a commit that changed
`.transcrypt/config`, your stored key no longer matches. Pulled files stay
encrypted, `status` says so, and `git add` refuses plaintext until you run
`transcrypt-v3 unlock` with the new passphrase.

**Work from before a rekey.** A commit cherry-picked or rebased onto a
`rekey` keeps the records it was made with, under the earlier config. Git
keeps working, and smudge and `status` say which files are affected. Then:

```bash
transcrypt-v3 reencrypt        # asks for the earlier passphrase
git commit --amend --no-edit
```

Each such record is authenticated under the earlier config, at its own
path, and re-encrypted under the current one; the pre-commit hook and the
pre-push audit refuse to publish it until then. Only configs your branch
had before its current one are accepted, so `reencrypt` never moves newer
content back under a revoked passphrase. Do it only for your own work: the
content becomes trusted under the current config.

All worktrees of a clone share one stored key. Unlocking a worktree that
is on a commit from before a rekey replaces it, and the other worktrees
then need `unlock` again.

## Merging

Protected files merge like ordinary text. The `transcrypt` macro selects a
merge driver that:
1. decrypts both sides and their base;
2. merges the plaintexts in a private scratch directory under `.git`;
3. stores the result encrypted.

On a conflict, the file shows the usual `<<<<<<< ours` / `>>>>>>> theirs`
markers in plaintext. Edit it, then `git add` and commit as usual. Merging
needs the repository unlocked. A clone without the driver sees protected
files as binary and keeps your side.

**Renames across branches.** Git recognizes renames by content similarity.
A protected file re-encrypted for its new path shares no bytes with its old
record, so Git does not recognize the rename. If one branch renames a
protected file and another edits it, the merge reports
`CONFLICT (modify/delete)`. Both versions are decrypted in your worktree
(the edited old name and the renamed new one). Apply the edit to the new
name, `git rm` the old one, and commit. The same applies to `git log
--follow`, which does not follow protected files across renames.

## Keep plaintext out of the remote

A protected file only gets encrypted in a checkout where `init` or `unlock`
installed the filters. In a fresh clone that never ran `unlock`,
`git add .env` stores **plaintext**, and no hook runs there. Two checks
catch this:

- The `pre-push` hook installed by `init`/`unlock` audits every commit you
  push, including merges, rebases and `--no-verify` commits. A merge commit
  is also verified before it is made (`pre-merge-commit`).
- `transcrypt-v3 audit <rev-list arguments>` needs no key. Run it in CI or a
  server hook to refuse plaintext from any checkout. Each commit is judged
  by its own `.gitattributes`. Without the key, the audit checks that every
  protected file is a v3 record for the committed config, and that no record
  was moved to another path without re-encryption. That stops accidental
  plaintext, not a deliberately forged record; when unlocked, the audit also
  authenticates every record.

For example, in GitHub Actions (any CI works the same way):

```yaml
- uses: actions/checkout@v4
  with: { fetch-depth: 0 }
- run: cargo install --locked --path rust/crates/transcrypt-v3   # or a released binary
- run: transcrypt-v3 audit --all     # every commit on every branch; no key needed
```

On a self-hosted server, install
[`contrib/v3/pre-receive`](../../contrib/v3/pre-receive) as the bare
repository's `hooks/pre-receive`, with `transcrypt-v3` on its `PATH` (or
`TRANSCRYPT_V3` set to it). It refuses more than 20000 commits per ref
(`TRANSCRYPT_V3_MAX_COMMITS`). Confirm either setup with
`contrib/v3/check-remote-enforcement <remote>`. It pushes a harmless
plaintext canary to a throwaway branch, and reports `ok` only if the remote
rejects it.

For scripts, `init`, `unlock`, `rekey` and `migrate` accept `--password-stdin`.

## Moving from Bash transcrypt (v2)

Run this in a checkout where Bash transcrypt is set up and has decrypted
the files:

```bash
transcrypt-v3 migrate        # choose the new v3 passphrase
git commit -m "Convert to transcrypt-v3"
```

`migrate`:
- refuses unless everything is committed and every v2-protected file holds
  plaintext;
- rewrites each `filter=crypt diff=crypt merge=crypt` rule (any context) to
  `transcrypt`, keeping your patterns;
- initializes v3 and re-encrypts those files with it.

Nothing is lost if it fails: the worktree plaintext is never modified, and
the attribute files and hooks are restored. It sets aside the Bash
pre-commit hook. It leaves the v2 configuration in place, including the v2
password in `.git/config`.

Then clone the repository afresh and check that `transcrypt-v3 unlock`
decrypts it. After that, remove the v2 credentials with
`git config --remove-section transcrypt` and `rm -r .git/crypt`. Earlier
commits keep their v2 ciphertext, readable with the v2 password. v2 used
unauthenticated CBC, and its password sat in plaintext in `.git/config`. If
that password or any of that history may have been exposed, change the
secrets themselves. Multiple v2 contexts become one v3 passphrase.

## What to expect

- **Equal plaintexts leak equality** at the same path in the same repository
  (deterministic encryption keeps Git diffs and merges stable).
- **`git diff` shows decrypted changes while unlocked.** Each version is
  authenticated at its own path, and nothing is cached: unlike Bash
  transcrypt's textconv cache, no plaintext is kept in `refs/notes`. While
  locked, Git only reports that the files differ.
- **Rollback is not detected.** Someone who controls your Git history can
  restore an older valid version of a protected file.
- **Hooks are local.** `git push --no-verify`, a clone that never ran
  `unlock`, or a server without `transcrypt-v3 audit` is not checked. If
  `core.hooksPath` is set, Git ignores `.git/hooks`; `status` and `doctor`
  warn.
- **Local attribute files apply.** A `filter` rule in
  `.git/info/attributes` or your global attributes file can unprotect files
  in this checkout only. `doctor` reports it, the pre-commit hook warns, and
  a server-side audit (which uses the committed rules) still refuses the
  plaintext.
- **Old history.** Checking out a commit encrypted under an earlier config
  (before a `rekey`) leaves its protected files encrypted, unless you unlock
  with that config's passphrase.
- **Hunk selection treats protected files as binary.** `git add -p`,
  `git checkout -p` and `git stash -p` work on Git's internal form of a
  file, which is the ciphertext. Stage protected files whole.
- Files larger than 16 MiB are refused.

## Troubleshooting

| Message | Meaning and fix |
| --- | --- |
| `this checkout is locked; run transcrypt-v3 unlock` | No key: `transcrypt-v3 unlock` |
| `the stored key does not match .transcrypt/config (it was rekeyed?)` | Someone changed the passphrase: `transcrypt-v3 unlock` with the new one |
| `this record does not open at PATH` | A file you moved with `git mv`: `git add PATH` (or commit). Otherwise a commit moved or altered the record (broken or hostile); do not merge it, or restore the file from a good commit |
| `PATH holds the encrypted OTHER: a renamed or copied protected file must be committed while unlocked` | Unlock, then commit; the hook re-encrypts it |
| `PATH is encrypted for another config (from before a rekey?)` / `other config (reencrypt)` | `transcrypt-v3 reencrypt` with that config's passphrase, then commit |
| `.gitattributes already defines the transcrypt macro differently` | Remove or rename that `[attr]transcrypt` line; v3 needs the macro to set the filter |
| `moved here without re-encryption` (audit) | A commit moved a record without the hook (`--no-verify`, or locked): redo the move while unlocked |
| `the committed file is not v3 ciphertext` | Plaintext was committed at a protected path without the filter: rewrite that commit, and change the secret if it was pushed |
| `refusing double encryption` | You tried to add a file that is already a v3 record; restore the plaintext instead |
| `PATH is selected for encryption, but v3 never encrypts .gitattributes, .gitmodules or .transcrypt/` | Narrow the `.gitattributes` pattern |
| `unsafe .git/transcrypt-v3...` | A credential or staging path is a symlink, has loose permissions or belongs to another user; remove it and unlock again |
| `another transcrypt-v3 hydrate or lock is running` | Wait for it to finish |
| `protected worktree file changed after it was checked` | Something wrote the file during `lock`/`hydrate`; rerun the command |
| `refusing to push` / `not v3 ciphertext for its configuration (plaintext?)` | A commit contains an unencrypted protected file: rewrite it out of the unpushed history (for example `git rebase -i`), and change the secret if it was ever pushed |

## What is and is not proved

The pure Rust protocol core (`rust/crates/transcrypt-v3-core`) is
translated to Lean by Charon/Aeneas and proved against an independent
specification:
- the exact on-disk formats;
- the canonical-path policy (any valid Git path except repository
  metadata);
- the parsing of Git's attribute answers, which decide what is protected;
- that plaintext is released only for a record authenticated under the
  repository config and its exact path;
- that smudge keeps only genuine v3 envelopes and never presents other
  bytes as a protected file;
- that `lock` never discards unrecoverable plaintext and `hydrate` only
  replaces exact staged ciphertext.

These guarantees assume:
- the cryptographic primitives behave as AES-SIV, Argon2id and SHA-256;
- Git evaluates attributes and invokes the filters as documented;
- the unverified Git/OS adapter follows the modeled steps.

You choose which files are selected; no proof covers that choice. Where the
key waits (stored or in the private agent) does not change the ciphertext.
See [V3-ASSUMPTIONS.md](V3-ASSUMPTIONS.md) for the exact, trust-ordered list
and [V3-PROOF-COVERAGE.md](V3-PROOF-COVERAGE.md) for theorem names.
