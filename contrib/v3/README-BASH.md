# transcrypt-bash: the portable Transcrypt v3 client

`transcrypt-bash` is a complete Transcrypt v3 client written in Bash. It
needs only Bash 4+, Git, the **OpenSSL 3 command line** (3.0.13 or newer)
and POSIX utilities (`od`, `head`, `tail`, `wc`, `cmp`, `diff`, `mktemp`):
no Rust binary, Python or compiled helper. Use it where the Rust client
(`transcrypt-rs`) is not available; both work on the same repositories.

**Same repositories, same bytes.** For the portable profiles both clients
write the identical `.transcrypt/config`, the identical encrypted Git
objects and the identical local key file. A repository set up by one can be
cloned, unlocked, edited, merged, rekeyed and audited with the other; in one
checkout you can switch clients without unlocking again.

## Profiles

| Profile | Key derivation | transcrypt-bash | transcrypt-rs |
| --- | --- | --- | --- |
| `scrypt` (2) | scrypt N=2^15, r=8, p=1 | yes (the default) | yes |
| `pbkdf2` (3) | PBKDF2-HMAC-SHA256, 600 000 iterations | yes | yes |
| `argon2id` (1) | Argon2id 64 MiB, t=3 | no: OpenSSL 3.0 has no Argon2id | yes (its default) |

Every profile encrypts files with AES-256-SIV bound to the repository
configuration and the file's exact Git path. Profiles differ only in how the
passphrase becomes a key: scrypt and Argon2id are memory-hard and slow down
offline guessing more than PBKDF2; a long random passphrase matters more than
the profile. In a profile-1 repository `transcrypt-bash` says so and changes
nothing; `transcrypt-rs rekey --profile=scrypt` makes it portable.

## Use

```bash
# Set up (from the repository root); then commit
transcrypt-bash init '.env' 'secrets/**'          # asks for a passphrase twice
git commit -m 'Enable transcrypt-v3'

# A fresh clone: unlock once; files decrypt and Git works normally
git clone URL && cd REPO
transcrypt-bash unlock

# Everyday work is plain Git: edit, add, commit, diff, merge, git mv
transcrypt-bash status
transcrypt-bash protect 'config/*.key'             # encrypt more files
transcrypt-bash unprotect 'config/*.key'           # publish them as plaintext from now on
transcrypt-bash rekey [--profile=pbkdf2]           # new passphrase (and profile); commit after
transcrypt-bash lock                               # ciphertext back in the worktree, key forgotten
transcrypt-bash audit origin/main..HEAD            # check what you are about to publish
transcrypt-bash migrate                            # convert a Bash transcrypt (v2) checkout
transcrypt-bash reencrypt                          # files cherry-picked across a rekey
transcrypt-bash doctor                             # filters, hooks, OpenSSL capabilities, index
```

`--password-stdin` reads the passphrase from standard input (scripts, CI);
`TRANSCRYPT_PASSWORD` also works. Passphrases are 16 to 4096 bytes.

`unlock` (and `init`) store the derived key, never the passphrase, in
`.git/transcrypt-v3/key` (mode 0600), install the Git filters and the
`pre-commit`, `pre-push` and `pre-merge-commit` hooks, and decrypt the
worktree. Switching to `transcrypt-rs` in the same checkout is
`transcrypt-rs unlock` (the stored key is reused only after it authenticates);
back again is `transcrypt-bash install`.

## What protects you

- **Committed files are authenticated ciphertext.** The clean filter
  encrypts; the `pre-commit` hook encrypts anything staged around the filter
  and re-encrypts files you renamed with `git mv`, and refuses records that
  were not sealed for their path. It never re-encrypts content that came
  from another commit (no laundering).
- **Decryption is exact or fails.** A record opens only at its own path
  under its own configuration; anything altered, moved, truncated or of
  another configuration is refused, and unauthenticated bytes are never
  written out.
- **Pushes are audited.** The `pre-push` hook checks every outgoing commit,
  not only the last one, using each commit's own `.gitattributes` and
  config: a plaintext commit hidden behind a later fix is refused. Commits
  under a configuration this checkout has no key for (before a rekey) are
  checked by envelope; set `git config transcrypt.requireAuthenticatedPush
  true` to refuse those instead.
- **No downgrade.** The profile comes from the committed config, which the
  passphrase authenticates; an unknown or unsupported profile is refused by
  name before anything changes, and a failed key derivation or OpenSSL call
  is an error, never a fallback to plaintext or a weaker setting.

Local hooks protect against mistakes, not against someone who disables them;
enforce publication with `audit` in CI or a server hook
(`contrib/v3/pre-receive`). Filenames, sizes, history structure and the
equality of a file's content between commits stay visible. Data committed
before it was protected stays in earlier commits.

## Differences from transcrypt-rs

The portable client is slower: a few OpenSSL processes per file. On a
repository with 100 protected and 200 other files (Linux, OpenSSL 3.0.13),
`git status` takes 0.1 s, a commit 1.3 s, a checkout switching 10
protected files 1.4 to 1.8 s, `lock` and `unlock` (every file) about 16 s
(37 s and 27 s before the scratch hand-off of 2026-11-11, measured back to
back on the same, busy, machine), and the first commit after a
`.gitattributes` change 7 to 9 s (every protected file is authenticated
then); `transcrypt-rs` does each in about a second or less. It keeps derived keys in
local OpenSSL arguments and plaintext in a private (0700) scratch
directory in the checkout's Git directory while it works (a run that is
killed leaves it there; the next run removes it), and caches the verification of the stored key next
to it (`.git/transcrypt-v3/bash-verified`, removed by `lock`). Under the
Transcrypt threat model the developer's machine is trusted; none of this
reaches Git. `transcrypt-rs` additionally offers profile 1, the `--private`
mode (key only in a memory-only agent, private file permissions), a
long-running filter process and in-memory key handling with zeroization.
The shared commands make the same security decisions;
`tests/v3/conformance/run.sh` checks them in real repositories in both
directions.

## If a command is interrupted

Nothing unencrypted reaches Git, whichever moment a command is killed at.
Rerun `lock`, `unlock` or `hydrate`; rerun `init` or `migrate` with the
same passphrase (an uncommitted `.transcrypt/config` is an interrupted setup,
which the rerun completes, protecting what the first run was asked to even
if the rerun names nothing). After an interrupted `rekey`,
`transcrypt-bash status` reports its journal: finish it with `rekey
--continue` (new passphrase) or undo it with `rekey --abort` (old
passphrase), which change only the entries the rekey staged and keep
everything else you staged; see "If `rekey` is interrupted" in the
[user guide](../../docs/verification/V3-USER-GUIDE.md). If Git then
reports `index.lock: File exists`, remove `.git/index.lock` as Git says.

## Known limitation: empty protected files and `git merge`

An **empty** protected file makes `git merge` stop with `fatal: stash
failed`, and `git diff` list the file as changed. This is a Git bug that
affects any clean filter turning an empty file into non-empty content (Git
marks such index entries as possibly modified forever and its merge then
misreads `git stash create`), in both clients. Put a byte in the file (for
example a newline) or do not protect empty files.

## Tests

```bash
bash tests/v3/bash/test_reference.sh            # this client alone (no Rust, no Python)
bash tests/v3/conformance/run.sh [transcrypt-rs] # both clients, both directions
bash tests/v3/conformance/lifecycle.sh           # rebase/cherry-pick/stash across clients;
                                                 # init/rekey/lock/unlock/migrate killed at every call
python3 tests/v3/reference/portable_vectors.py  # regenerate/check the independent vectors
```

The byte format is in
[V3-PORTABLE-PROFILES.md](../../docs/verification/specs/V3-PORTABLE-PROFILES.md).
