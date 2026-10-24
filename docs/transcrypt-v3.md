# Transcrypt v3: authenticated deterministic encryption

> This is a **pre-release candidate**, not a completed security audit. It is
> implemented in Bash and OpenSSL, and requires cross-platform testing and
> independent cryptographic review before a general-purpose stable release.

The original legacy format uses OpenSSL's old password derivation and a
password-derived salt. The latter permits inexpensive offline checks of
password guesses before running a slow KDF. Simply passing `-pbkdf2` to the
old implementation would therefore **not** fix its brute-force weakness.

Transcrypt v3 provides:

- A committed **non-secret** `.transcrypt/config` recording format, cipher,
  PBKDF2 iteration count, digest, authentication and a repository salt.
- PBKDF2-HMAC-SHA256 executed *before* deriving any secret per-file values.
- Separate encryption, authentication and IV keys derived with distinct HMAC
  labels from the PBKDF2 result.
- Deterministic AES-256-CBC encryption with a synthetic IV derived from the
  entire plaintext, and an HMAC-SHA256 over the versioned ciphertext envelope.
- **Verify before decrypt**: malformed or unauthenticated v3 ciphertext
  causes a nonzero filter exit without emitting any plaintext or fallback blob.
- Legacy v2 remains readable under its original configuration. It is never
  interpreted as v3 based solely on a user-controlled filename extension.
- A staged, explicit migration operation with preflight checks and a temporary
  Git index. Conversion does not rewrite earlier commits.

## Initialize a new repository

```bash
# In a new Git repository with no encrypted history:
transcrypt --format=v3 --yes
# Apply .gitattributes encryption patterns as usual and stage the public config:
git add .transcrypt/config .gitattributes
```

New repositories with no existing HEAD commit select v3 by default, including
when the `--format` flag is omitted. `--format=legacy` explicitly selects the
old format. Clones with existing encrypted history must be unlocked using the
format specified by their committed `.transcrypt/config`, if present, or the
legacy format otherwise. **Do not add v3 settings manually to old ciphertext.**

The public config looks like:

```ini
[transcrypt]
format = v3
cipher = aes-256-cbc
digest = sha256
kdf = pbkdf2
iterations = 250000
base-salt = 0123456789abcdef0123456789abcdef
auth = hmac-sha256
```

The example salt is illustrative, not a recommended value to copy. New
repositories use `openssl rand -hex 16`. Public config is authoritative, and
must contain no password, secret key or local OpenSSL path. The optional flags
`--iterations=COUNT` and `--base-salt=32_HEX_CHARS` select parameters when a
new v3 config is first created or during an explicit migration. Once committed,
these settings must not be edited without re-encrypting all data.

## Migrate an existing v2 repository

All collaborators should have a compatible v3-capable transcrypt installation
**before the migration commit is pulled**. Commit or stash any changes, and
make a backup. Unlock every configured encryption context locally first.

```bash
# This command works on the v3-capable executable, not the old installed copy.
transcrypt --migrate-v3 --yes
# Inspect the staging area, which includes .transcrypt/config and all ciphertext:
git diff --cached --stat
# Commit everything atomically, including all encrypted blobs and the public config.
git commit -m 'Migrate transcrypt secrets to authenticated v3'
```

Migration rejects dirty tracked files, unsupported settings, unavailable
credentials, or any legacy plaintext that fails to reconstruct its original
Git blob byte-for-byte. The operation stages changes in an alternate index;
if encryption or verification fails, it restores the prior index, public
config and installed helper script. It does **not** modify Git history.
Historical v2 commits remain legacy, so opening historical snapshots and
textconv diffs from the old format can require an older compatible checkout.
Also, historical weakly encrypted blobs remain in the repository's reachable
history. For compromised secrets, **rotate the secrets**, rather than assuming
re-encryption protects earlier history.

### Existing collaborator clones

A collaborator with an **already-installed legacy clean/smudge filter** should
flush its legacy credentials **before** pulling the migration commit, so the
checkout does not attempt to decrypt new v3 records as legacy ciphertext.
After the pull, use the v3-capable executable to reinitialize each context
using the committed public settings and the appropriate context password. Do
not discard local uncommitted secret edits when flushing or resetting; work
from a backed-up clean checkout. Alternatively, clone the migrated repository
afresh, install v3-capable Transcrypt and unlock it there.

To change the password in an existing v3 repo, use the normal
`transcrypt --rekey` operation: the public salt remains stable, and changed
ciphertext is staged for a separate commit.

## Ciphertext format and threat model

The wire format is one ASCII line (with a trailing newline):

```text
TCRYPT3:<32 lowercase hex IV>:<64 lowercase hex HMAC>:<base64 ciphertext>
```

1. A public 128-bit repository salt (from `.transcrypt/config`) and the context
   name are hashed and truncated to the 8-byte salt required by OpenSSL's
   `enc -S` compatibility interface. PBKDF2-HMAC-SHA256 derives a 32-byte
   master key using the committed iteration count. The password is passed to
   OpenSSL through `-pass env:ENC_PASS`, not a command-line argument.
2. Independently labelled HMAC-SHA256 derivations yield encryption, MAC, and
   IV-generation keys.
3. A keyed HMAC of the whole plaintext with a fixed domain label supplies a
   128-bit synthetic IV, making encryption deterministic as required by Git's
   clean/smudge filters.
4. AES-256-CBC with PKCS#7 padding encrypts using `-K` and `-iv`.
5. HMAC-SHA256 authenticates the exact ASCII `TCRYPT3:IV:ciphertext` string.
   Decryption checks this MAC **before** base64-decoding and decrypting;
   it also checks the reconstructed synthetic IV before releasing plaintext.

This format is *deterministic*, not semantically secure under chosen-plaintext
attacks. Files with identical plaintext under the same password, salt and
context yield identical ciphertext, and ciphertext length reveals approximate
plaintext size. It does not bind the file path, which allows encrypted files
to be renamed without invalidating authentication. HMAC detects malicious
bit-level modifications of blobs by actors **without the key**, but it does
not provide authenticity or rollback protection against those who know the
password or can substitute another valid encrypted file. For a future format,
standardized misuse-resistant AEAD (e.g. AES-SIV) is preferable where
portable tooling is available; this candidate avoids a new runtime dependency.

Both OpenSSL and LibreSSL behavior should be tested on every supported platform.
Old versions without `enc -pbkdf2 -iter`, `dgst -mac` or suitable base64 support
cannot use v3; installation should fail explicitly rather than downgrade. The new implementation passes **derived AES/HMAC keys in OpenSSL command-line
options** (`enc -K` and `dgst -macopt hexkey:`), because the portable `openssl`
CLI lacks a simple file-descriptor interface for those options. On systems
where local processes' arguments can be inspected by other users, this is a
key-exposure risk and is a release-blocking concern to resolve or constrain
before handling high-value secrets. As in previous Transcrypt versions,
plaintext exists on local disk while unlocked; keep workstations trusted.

The
new format does not depend on a Python runtime. No Argon2 or scrypt mode is
advertised or implemented yet; the config file is versioned for future work.

## Support boundaries

- `--upgrade` updates installed helper scripts without changing stored
  public parameters. All named contexts use independent local passwords.
- `--uninstall` removes the working-tree public configuration; existing
  committed metadata and historical ciphertext remain in Git history.
- Legacy v2 encryption is preserved when explicitly requested, including its
  historical OpenSSL warning and its old ciphertext representation.
- Zero-length files are not encrypted, as in v2. The pre-commit hook checks
  ciphertext markers; authenticated v3 validation takes place on decrypt.
- A new cryptographic version should undergo independent review and portable
  Bats CI before merging to `main`.

## Related upstream plan

See [issue #134](https://github.com/elasticdog/transcrypt/issues/134#issuecomment-4478657672),
[PR #210](https://github.com/elasticdog/transcrypt/pull/210),
[PR #211](https://github.com/elasticdog/transcrypt/pull/211), and
[the v3 integration PR #219](https://github.com/elasticdog/transcrypt/pull/219).
The cryptographic work belongs on the separate `transcrypt-v3` integration
branch until the maintainer accepts a release and compatibility policy.
