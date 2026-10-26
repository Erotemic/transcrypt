# Transcrypt v3 (Rust)

`transcrypt-v3` encrypts the files you choose in a Git repository with
Argon2id and AES-256-SIV, binding each record to its exact path. The user guide
is [`docs/transcrypt-v3.md`](../docs/transcrypt-v3.md); the current status,
proof boundary and assumptions are in
[`V3-HANDOFF.md`](../docs/verification/V3-HANDOFF.md),
[`V3-SECURITY-ARGUMENT.md`](../docs/verification/V3-SECURITY-ARGUMENT.md) and
[`V3-ASSUMPTIONS.md`](../docs/verification/V3-ASSUMPTIONS.md).

Crates:

- `transcrypt-v3-core`: the pure `no_std` core (wire formats, policy
  decisions, Git snapshot queries), extracted to Lean and proved against an
  independent specification (`proofs/aeneas`).
- `transcrypt-v3`: the CLI and its Git, filesystem, credential and crypto
  adapters.

```bash
cd rust
cargo test --workspace
cargo build --release -p transcrypt-v3
```

The first build fetches the pinned RustCrypto dependencies. Static release
binaries for Linux x86_64 and arm64 come from `scripts/build-release.sh`, with
or without CI; see [`docs/RELEASING.md`](../docs/RELEASING.md). The legacy-v2
compatibility crates are a separate workspace in [`../rust-legacy`](../rust-legacy).
