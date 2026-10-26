# Releasing transcrypt-v3

Release binaries are static Linux executables for **x86_64** and **arm64**
(aarch64). Each is one file with no dependencies except Git 2.34 or later at
run time: musl libc is linked in, and the cryptography is pure Rust (no
OpenSSL).

## Building without CI

```bash
scripts/build-release.sh --test        # both archives into dist/, tests on this machine's architecture
scripts/build-release.sh aarch64-unknown-linux-musl   # one target
```

The script needs only `rustup`, Git, GNU `tar`, `gzip` and `sha256sum`. It
installs the pinned Rust toolchain and targets itself, and links with Rust's
bundled `rust-lld`, so any Linux machine of either architecture builds both
archives (no C cross toolchain, no Docker). `--test` runs the v3 test suite
against the static binary of each target the machine can execute; arm64
tests need an arm64 machine (or `qemu-user` binfmt).

The output in `dist/` is:

- `transcrypt-v3-<version>-x86_64-linux.tar.gz`
- `transcrypt-v3-<version>-aarch64-linux.tar.gz`
- `SHA256SUMS`

Each archive holds `transcrypt-v3`, `LICENSE` and the user guide as
`README.md`. The script refuses a working tree with uncommitted changes
(`--allow-dirty` overrides, and the binary's `transcrypt-v3 --version` then
says `-dirty`).

**Reproducibility.** The toolchain is pinned (`RUST_TOOLCHAIN`, default
in the script), paths are remapped, the binary is stripped, built with one
codegen unit and LTO, and the archive's timestamps and owners come from the
commit. Rebuilding a tag at any path on the same architecture gives the same
`SHA256SUMS`. Whether an x86_64 and an arm64 *host* build identical
binaries is checked, and reported, by every release run.

## Releasing with GitHub

1. Bump `version` in `rust/crates/transcrypt-v3/Cargo.toml` and commit.
2. Tag the commit `v3-<version>` (for example `v3-0.1.0`) and push the tag.
3. `.github/workflows/release.yml` builds both archives on an x86_64 and an
   arm64 runner with the same script, tests each natively, compares the two
   runners' builds, adds GitHub build-provenance attestations and creates a
   **draft** release. Check it, then publish it.

A manual run of the workflow (`workflow_dispatch`) builds and tests without
releasing.

## Installing

```bash
curl -fsSLO https://raw.githubusercontent.com/Erotemic/transcrypt/master/scripts/install.sh
sh install.sh                     # newest v3 release into ~/.local/bin
sh install.sh --tag v3-0.1.0 --prefix /usr/local
sh install.sh --from dist/        # archives built locally, no network
```

The installer checks the archive against `SHA256SUMS` before installing.
`SHA256SUMS` comes from the same place as the archive, so it detects
corruption, not a compromised release; for that, check the attestation
(`gh attestation verify <archive> --repo Erotemic/transcrypt`) or rebuild
the tag and compare checksums.

## Platform roadmap

Done: Linux x86_64 and arm64, static, tested natively in CI.

| Platform | State | What remains |
| --- | --- | --- |
| Linux riscv64, armv7 (32-bit) | compiles (`cargo check`); the Lean proofs cover 32- and 64-bit `usize` | add targets to the script; test under QEMU (`cross test`) or on hardware |
| macOS (arm64, x86_64) | builds and is tested in CI from source | universal binary (`lipo`), signing and notarization (Apple developer account) so downloaded binaries open without a warning |
| FreeBSD | compiles | build on FreeBSD or with `cross`; run the suite in a VM (`vmactions/freebsd-vm`) |
| NetBSD | two compile errors (stat timestamp field names in `fsat.rs`) | fix; build and test in a VM |
| OpenBSD | not checked (no prebuilt Rust standard library) | build and test natively in a VM |
| Windows | not supported (`main.rs` refuses non-Unix) | a port of the security-relevant layer: handle-relative safe writes, an owner-only ACL on the stored key, the private-mode agent over a named pipe with client-token checks, path and mode handling; new entries in the assumption register and an adversarial review. WSL works with the Linux binary today |

Every new platform needs the test suite passing on it, not only a build:
the safe-write layer, `flock`, socket peer credentials and `mlock` are
platform behaviour that the adapter's assumptions (V3-ASSUMPTIONS) rely on.
Further distribution channels (Homebrew, distribution packages, `cargo
install` from crates.io) and signing archives with a key held outside GitHub
(minisign or Sigstore) follow the same order.
