# Releasing transcrypt-rs

Release archives exist for these systems. Each holds one executable and
needs nothing at run time but Git 2.34 or later (on Windows, Git for
Windows). The cryptography is pure Rust (no OpenSSL).

| System | Archive | Binary | Where it is tested |
| --- | --- | --- | --- |
| Linux x86_64, arm64 | `transcrypt-rs-<version>-{x86_64,aarch64}-linux.tar.gz` | static (musl) | the whole suite on both architectures (CI; locally on x86_64, Git 2.34 and current) |
| FreeBSD 14.4 and later, x86_64 | `transcrypt-rs-<version>-x86_64-freebsd.tar.gz` | base libraries only (`libc.so.7`, `libthr`, `libgcc_s`) | the whole suite against the release binary in a FreeBSD VM (CI; locally on 14.5) |
| macOS arm64, x86_64 | `transcrypt-rs-<version>-{aarch64,x86_64}-macos.tar.gz` | system libraries only | the whole suite on a macOS runner (CI only: not run outside GitHub so far) |
| Windows 10 1803+ / Server 2019+, x86_64 | `transcrypt-rs-<version>-x86_64-windows.zip` | static CRT, system DLLs only | the whole suite against the release binary on a Windows runner (CI; locally on Windows Server 2025 as a non-administrator) |

Each archive holds `transcrypt-rs` (`transcrypt-rs.exe` on Windows),
`LICENSE` and the user guide as `README.md`.

## Building without CI

```bash
scripts/build-release.sh --test    # every archive this machine builds, into dist/
scripts/build-release.sh x86_64-unknown-freebsd   # one target
```

On **Linux** the script builds the Linux, FreeBSD and Windows archives; on
**macOS**, the two macOS archives. It needs `rustup`, Git, GNU `tar` (as
`tar` or `gtar`), `gzip` and `sha256sum` (or `shasum`), and per target:

- Linux: nothing more. Rust's bundled `rust-lld` links musl.
- FreeBSD: `clang`. The script downloads the base set of the pinned FreeBSD
  release (`base.txz`, checked against the SHA-256 in the script) and links
  against its libraries, so the binary runs on that release and later ones.
- Windows: mingw-w64 (`x86_64-w64-mingw32-gcc`, `-objdump`) and `python3`
  (for a zip with stored entries, whose bytes depend on no zlib version).
- macOS: the Xcode command-line tools.

It installs the pinned Rust toolchain and targets itself. Each binary is
checked before it is archived: no ELF interpreter for Linux, only FreeBSD
base libraries, only `/usr/lib` and `/System` libraries on macOS, only DLLs
that Windows ships. `--test` runs the suite against every binary this
machine can execute. Test another system's archive on that system against
its own binary:

```bash
TRANSCRYPT_RS_TEST_BIN=/path/to/transcrypt-rs cargo test --locked -p transcrypt-rs   # in rust/
```

The script refuses a working tree with uncommitted changes (`--allow-dirty`
overrides; `transcrypt-rs --version` then says `-dirty`).

**Reproducibility.** The toolchain is pinned (`RUST_TOOLCHAIN`, default in
the script), paths are remapped, binaries are stripped and built with one
codegen unit and LTO, and archive timestamps and owners come from the
commit. Rebuilding a tag at any path on the same host gives the same
`SHA256SUMS`. Every release run builds the Linux archives on an x86_64 and
an arm64 host and reports whether they differ.

## Continuous integration

Every push to `master` or a `work/**` branch, and every pull request, runs
`.github/workflows/run-bats-core-tests.yml`:

- shell lint (`scripts/lint-shell.sh`, pinned shellcheck and shfmt);
- the Bash v2 and v3 Bats suites (Ubuntu 22.04 and 24.04, macOS);
- both Rust workspaces on Linux x86_64 (Git 2.34 and current) and arm64,
  macOS and Windows (MSVC toolchain), and in a FreeBSD 14.4 VM, with
  clippy (warnings are errors) and `cargo audit`; the legacy-v2 parity
  tests everywhere but Windows (Bash transcrypt never supported it);
- the static Linux release archives, built and installed;
- the proofs on Linux, macOS and Windows: the Lean specification, the
  generated-code refinement build and the axiom audit; re-extraction with
  the pinned translator on Linux.

## Releasing with GitHub

1. Bump `version` in `rust/crates/transcrypt-rs/Cargo.toml` and commit.
2. Tag the commit `v3-<version>` (for example `v3-0.1.0`) and push the tag.
3. `.github/workflows/release.yml` builds every archive with the same
   script (Linux, FreeBSD and Windows on an x86_64 Linux runner, the Linux
   archives again on arm64, macOS on a macOS runner), runs the suite against
   the Windows binary on Windows and the FreeBSD binary in a FreeBSD VM,
   compares the two Linux builds, collects one `SHA256SUMS`, adds GitHub
   build-provenance attestations and creates a **draft** release. Check it,
   then publish it.

A manual run of the workflow (`workflow_dispatch`) builds and tests without
releasing.

## Installing

Linux, FreeBSD and macOS:

```bash
curl -fsSLO https://raw.githubusercontent.com/Erotemic/transcrypt/master/scripts/install.sh
sh install.sh                     # newest v3 release into ~/.local/bin
sh install.sh --tag v3-0.1.0 --prefix /usr/local
sh install.sh --from dist/        # archives built locally, no network
```

Windows (PowerShell):

```powershell
Invoke-WebRequest -UseBasicParsing https://raw.githubusercontent.com/Erotemic/transcrypt/master/scripts/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File install.ps1    # into %LOCALAPPDATA%\transcrypt-rs\bin, added to PATH
```

Both installers check the archive against `SHA256SUMS` before installing.
`SHA256SUMS` comes from the same place as the archive, so it detects
corruption, not a compromised release; for that, check the attestation
(`gh attestation verify <archive> --repo Erotemic/transcrypt`) or rebuild
the tag and compare checksums.

On macOS, a binary downloaded with a browser carries the quarantine
attribute and Gatekeeper refuses it, because release binaries are not
notarized; the installers download with `curl`, which sets no quarantine
(or run `xattr -d com.apple.quarantine transcrypt-rs`).

## Platform notes and roadmap

- **Windows** needs Git for Windows: its `sh` runs the hooks and filter
  commands. The private mode (`unlock --private`) uses Windows' Unix-domain
  sockets (Windows 10 1803 and later). Git paths must be valid UTF-8
  (Windows file names are Unicode), and Git for Windows' default
  `core.autocrlf=true` leaves protected files alone (the `transcrypt` macro
  sets `-text`). A repository under OneDrive or another reparse-point
  provider is refused for protected files (reparse points are never
  followed).
- **macOS**: universal binaries (`lipo`) and notarization (Apple developer
  account) so that downloaded binaries open without a warning.
- **NetBSD** builds (`cargo check`, clippy); **OpenBSD** has no prebuilt Rust
  standard library: both need a VM run of the suite before release archives.
- **FreeBSD arm64, Windows arm64, Linux riscv64 and armv7**: the code
  compiles for these; each needs its target in the script and a native (or
  emulated) test run. The Lean proofs cover 32- and 64-bit `usize`.

Every new platform needs the test suite passing on it, not only a build:
the safe-write layer, the staging lock, the agent socket's peer check and
file privacy are platform behaviour that the adapter's assumptions
(V3-ASSUMPTIONS, A8 and A25) rely on.
