# Migrating legacy configurable OpenSSL repositories

Some historical transcrypt deployments encrypted files with OpenSSL `enc` while
allowing configurable digest/KDF settings such as `transcrypt.digest=sha256` and
`transcrypt.kdf=pbkdf2`. Modern transcrypt secure mode uses an authenticated v3
envelope, so these repositories should be migrated rather than treated as
ordinary legacy repositories.

Use the standalone helper on a clean checkout of a legacy configurable OpenSSL
repository:

```bash
# From the repository root, using this branch's transcrypt and helper scripts:
tools/transcrypt-migrate-legacy-openssl --password='your existing password' --yes

# Review the staged migration, then commit it:
git diff --cached --textconv
git commit -m "Migrate legacy OpenSSL encryption to authenticated v3"
```

The helper reads the existing `transcrypt.cipher`, `transcrypt.digest`, and
`transcrypt.kdf` settings from local Git config or `.transcrypt/config`, then
performs these steps:

1. Finds tracked files with `filter=crypt` or `filter=crypt-*` attributes.
2. Decrypts the current `HEAD` ciphertext with the legacy OpenSSL settings.
3. Reinitializes modern transcrypt secure mode with `--rekey`.
4. Re-adds the files so they are staged as authenticated v3 ciphertext.

A legacy deterministic `base-salt` is not needed for decryption because each
OpenSSL `Salted__` blob stores the salt needed by `openssl enc -d`. The migrated
repository receives a new public v3 repository salt in `.transcrypt/config`.

Useful options:

```bash
tools/transcrypt-migrate-legacy-openssl \
  --password='your existing password' \
  --digest=sha256 \
  --kdf=pbkdf2 \
  --iterations=256000 \
  --yes
```
