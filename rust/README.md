# Rust distribution of Transcrypt

There is now an **executable Rust legacy-v2 filter adapter**, with its pure
protocol and policy kernels split out for later Charon/Aeneas refinement. This
is a second implementation of the old released format, not a completed
modern authenticated encryption implementation or an independent security
review. The Bash program remains installable and usable on its own.

## Build and test (no Cargo registry dependencies)

```bash
cd ~/code/transcrypt/rust
cargo test --offline
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
