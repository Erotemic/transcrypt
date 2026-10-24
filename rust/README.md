# Rust distribution of Transcrypt

There is now an **executable Rust legacy-v2 filter adapter**, with its pure
protocol and policy kernels split out for later Charon/Aeneas refinement. This
is a second implementation of the old released format, not a completed
modern authenticated encryption implementation or an independent security
review. The Bash program remains installable and usable on its own.

## Legacy-v2-only builds

The v2 crates have no registry dependencies, but the **workspace now contains
v3 crates that need an initial online dependency resolution**. Use
`cargo test --workspace` for full CI. After the lockfile and dependencies are
cached, legacy-only builds work offline:

```bash
cd ~/code/transcrypt/rust
cargo test --offline -p transcrypt-legacy -p transcrypt-legacy-core -p transcrypt-protocol -p transcrypt-policy
cargo build --offline --release -p transcrypt-legacy
```

Crates:

- `transcrypt-protocol`: pure v2 byte parser / canonical serializer.
- `transcrypt-legacy-core`: `no_std` pure v2 HMAC transcript, salt selection,
  context-name grammar, and legacy discriminator — the next Aeneas target.
- `transcrypt-legacy`: `transcrypt-rs` CLI, Git config + OpenSSL process
  adapters for `clean`, `smudge`, and `textconv`. Uses exact legacy bytes.
- `transcrypt-policy`: small pure decision gates for the future secure
  protocol; **not yet attached to Git operations**.

`transcrypt-legacy` has no registry dependencies but **does require** the Git
and OpenSSL command-line tools at runtime, just like Bash. It uses the
legacy OpenSSL/MD5 scheme, including old credential exposure risks. Do not
recommend v2 for new secret repositories.

## Use in a previously initialized v2 repository

Bash still owns initialization, GPG import/export, rekeying, uninstall,
merge drivers, and the pre-commit hook. The Rust binary may replace only
the default-context Git clean/smudge/textconv filters as follows, after
building it above:

```bash
RUST_FILTER="$(cd ~/code/transcrypt/rust && pwd -P)/target/release/transcrypt-rs"

git config --local filter.crypt.clean "'$RUST_FILTER' clean context=default %f"
git config --local filter.crypt.smudge "'$RUST_FILTER' smudge context=default"
git config --local filter.crypt.required true
git config --local diff.crypt.textconv "'$RUST_FILTER' textconv context=default"
git config --local diff.crypt.cachetextconv false
```

Run these Git configuration commands **inside the already initialized
repository whose filters you are deliberately changing**. Keep Bash's
existing `merge.crypt.driver` and pre-commit hook until Rust equivalents are
implemented and reviewed. Named contexts use separate Git `filter.crypt-NAME`
and `diff.crypt-NAME` keys, with `context=NAME` in each command.

The filter CLI also accepts `clean PATH`, `smudge`, and `textconv PATH`
with the implicit default context. Failed crypto commands do not write
partial output, and `TCRYPT3:` inputs are rejected rather than silently
reprocessed under v2. **There is no Rust `--init`, rekey or migration yet.**
The binary rejects other operations explicitly; it never silently delegates
to a Bash shell command.

## Shared specification and formal boundary

See [`LEGACY-V2-INTEROPERABILITY.md`](../docs/verification/specs/LEGACY-V2-INTEROPERABILITY.md).
It defines the exact existing Bash output, pure transcript functions,
missing authentication, known v2 pass-through hazard, and hand-audit mapping.

`tests/interop/check-bash-legacy-contract.sh` checks the Bash reference
without Rust or Bats. `crates/transcrypt-legacy/tests/filter_parity.rs`
checks the **Rust binary versus Bash and real Git index objects** on public
fixtures, named contexts, binary/large files, and error paths. Existing v2
`bats` tests remain a separate suite.

The next formal step is to translate the actual `transcrypt-legacy-core`
source with Charon/Aeneas, then prove its result refines an independent Lean
byte specification; the crypto/OpenSSL and Git/OS adapters remain external
contracts. Standalone SMT exercises are not milestones for this project.
The final authenticated v3 suite remains blocked on the reviewed format and
portable Bash crypto decisions in `10-decisions-and-blockers.md`.

## Modern v3 secure-first prototype (independent of legacy)

The **new primary target** is `transcrypt-v3`, a separate executable with
no legacy crypto modes. Its fixed wire specification is
[`V3-AUTHENTICATED-P0.md`](../docs/verification/specs/V3-AUTHENTICATED-P0.md).
`transcrypt-v3-core` is a pure `no_std` parser/encoder intended for Aeneas.
`transcrypt-v3` uses Argon2id and RFC 5297 AES-SIV entirely in-process;
no password or derived key is passed to OpenSSL subprocess arguments.

Initial build requires fetching the pinned RustCrypto dependencies once:

```bash
cd rust
cargo test --workspace
cargo build --release -p transcrypt-v3
```

Minimal lifecycle in a new Git repository with a normal `.git` directory:

```bash
# cd into the repository after git init
/path/to/transcrypt/rust/target/release/transcrypt-v3 init
printf 'sensitive example\n' > example.secret
git add example.secret
git commit -m 'Add encrypted example'
```

The command will prompt for a passphrase; `--password-stdin` is supported
only for `init` and `unlock` in automated tests. Avoid invoking passphrases
as command-line arguments. New clones need:

```bash
/path/to/transcrypt/rust/target/release/transcrypt-v3 unlock
/path/to/transcrypt/rust/target/release/transcrypt-v3 hydrate
```

`hydrate` reads the authenticated **Git index** rather than HEAD, verifies
all protected worktree files before writing, and publishes plaintext without
running Git checkout/restore (whose clean filter can reject ciphertext).
It is safe to repeat after a partial hydration as long as existing protected
files still match staged ciphertext or its authenticated plaintext. Once
plaintext is present, it runs the clean filter to refresh Git's worktree stat
cache and verifies that the staged object IDs and modes did not change.
File replacement is atomic per file, not across the entire checkout.

Run `transcrypt-v3 lock` only after protected working files are committed.
It flushes tracked `*.secret` files to encrypted index bytes and removes
the credential agent. Unlock again and hydrate to resume.

**Key isolation:** a background process retains the 64-byte derived key in
memory. Git operations use `.git/transcrypt-v3/session.sock` (Unix socket
mode 0600, parent directory 0700) and **never receive the key itself**.
The key is never written to a local file by this version. If you previously
used the v3 prototype that wrote `.git/transcrypt-v3/key`, lock with that
version or remove that old on-disk key before running the new binary.
`lock` flushes protected files and stops the background process. Abruptly
killing the agent requires a new unlock; a stale socket is cleared safely
at next unlock. The agent trusts other processes under your Unix UID and
does not claim protection against swap or memory dumps.

**Remaining security limitations:** equality leakage under
AES-SIV, no path binding, no rollback resistance, no atomic multi-file lock,
no formally verified Git/OS adapter, and incomplete adversarial review remain.
The RustCrypto AES-SIV crate itself warns that it has not been independently
audited. Do not yet deploy for valuable secrets.

Reference vectors: `python3 tests/v3/reference/check_vectors.py -v`
(from repository root, with `cryptography` and `argon2-cffi` installed for
independent **development tests only**). Rust tests require no Python.
