# Bash v3 reference implementation

`transcrypt-bash` is a standalone, independent **profile-2** implementation
using Bash, Git, OpenSSL's command-line tools, and standard Unix utilities.
It does not call Rust, Python, Perl, `xxd`, or a compiled helper. Its crypto
format is defined in
[`../../docs/verification/specs/V3-PORTABLE-P2.md`](../../docs/verification/specs/V3-PORTABLE-P2.md).
The intended minimum OpenSSL version is **3.0.13**; initial executed tests
were on OpenSSL **3.5.5**. Use `bash --version`, `git --version`, and
`openssl version` to inspect the local environment. Bash 4+ is required.

```bash
# Run from a Git repository, with an installed copy of this script:
TRANSCRYPT_PASSWORD='a strong passphrase of your choice' \
  /path/to/transcrypt-bash init --profile v3-scrypt-aes256-siv '*.secret'
git commit -m 'Set up portable v3 encryption'

# On a new clone (install Git filters locally, then unlock and hydrate):
/path/to/transcrypt-bash install
TRANSCRYPT_PASSWORD='a strong passphrase of your choice' /path/to/transcrypt-bash unlock
/path/to/transcrypt-bash hydrate

# Ordinary Git work is then transparent:
printf 'sensitive bytes\n' > example.secret
git add example.secret
/path/to/transcrypt-bash verify-index
git commit -m 'Update protected data'
/path/to/transcrypt-bash audit HEAD

# If Git moved the file and staged its old-path ciphertext:
git mv example.secret moved.secret
/path/to/transcrypt-bash rebind

# To change the password and repository salt (commit changes first):
TRANSCRYPT_PASSWORD='a new strong passphrase' /path/to/transcrypt-bash rekey
git commit -m 'Rotate v3 portable encryption key'
```

The script provides `init`, `install`, `unlock`, `lock`, `protect`,
`unprotect`, `hydrate`, `rebind`, `rekey`, `clean`, `smudge`, `encrypt`,
`decrypt`, `verify-index`, `audit`, and `diff`/`merge` drivers. Run
`transcrypt-bash help` for their arguments. The explicit `unprotect`
operation stages **plaintext** intentionally and warns about it.

`install` sets *local* Git filter/merge/diff commands and installs
pre-commit, pre-push and pre-merge-commit hooks. The pre-push
hook audits **every outgoing commit**, rather than just `HEAD`, and refuses
a plaintext intermediate commit even when a later tree appears safe. It refuses to replace
unrelated existing hooks. The Git filter is `required=true`; failed filters
must not be ignored. A fresh clone without installed filters may nevertheless
stage plaintext if someone edits protected files before setup. Local hooks
are not a server-enforced policy; control remote writes with server-side
checks if a hostile or uninformed pusher is in scope. `audit REV` verifies
one tree using its own committed attributes and config. For a prior rekey,
it uses the locally retained `bash-key-p2.previous-<config-id>` credential.
A fresh clone without prior credentials may be unable to authenticate
previous history; it should not claim an unaudited push is safe.

Unlike the Rust client, Bash may expose derived keys in local OpenSSL
process arguments and write temporary plaintext to mode-0700 directories.
These are accepted trusted-host differences. Publication of plaintext to Git
is not accepted. The format authenticates ciphertext before emitting its
plaintext, and uses path/config binding.

Not implemented yet: profile 1 (Argon2id, available in Rust), profile 3,
Rust-side profile-2 interoperability, v2 migration, historical rekey browsing,
private-mode credential agent, complete Git-conflict recovery and the full
adversarial parity matrix. `rekey` requires a clean tracked working tree;
keep a backup of the original repository and test a disposable clone while
this backend is under development. The Bash script currently has no official
release/security qualification.

Tests (no Python required to run the precomputed independent vectors):

```bash
bash tests/v3/bash/test_reference.sh
```
