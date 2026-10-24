# Production v3 Rust extraction through Charon/Aeneas

The formal-verification target is the actual `transcrypt-v3-core` crate used
by the Rust executable. Its four fixed-width codec functions implement the
byte-level decisions modeled independently in `proofs/lean/Transcrypt/V3WireCodec.lean`.
The first obligation is to *extract* those four functions and compile their
Aeneas-generated Lean definitions. A later obligation is to prove that those
definitions refine the independent specification. Compilation alone does **not**
discharge the latter obligation.

## Tooling (Ubuntu/Linux)

Use the supported [hax 0.4 Lean backend](https://pereq.dev/hax/manual/lean/quick_start/)
instead of cloning or separately building Charon and Aeneas. `cargo-hax`
selects a matching Charon/Aeneas pair, downloads their prebuilt binaries,
checks their release-manifest hashes, and manages a compatible Lean package.
This has **no effect on the Bash or Rust runtime dependencies**; it is only
needed by developers verifying the Rust implementation.

With `rustup`, Cargo, and Lean (`elan`) installed:

```bash
cargo install --locked --version 0.4.2 cargo-hax
cd ~/code/transcrypt
bash proofs/aeneas/translate-v3-core.sh
bash proofs/aeneas/build-v3-generated.sh
```

The first command may download and compile `cargo-hax`. Its 0.4.2 version
output uses separate `version=0.4.2` and `commit=...` lines; the driver
script checks the exact version field rather than assuming a single line. The translation script
then validates the scenario with `cargo hax extract --dry-run v3-wire`,
installs matching tools via `cargo hax tools install`, and runs
`cargo hax extract v3-wire` from the actual crate directory. No `AENEAS_ROOT` environment variable or separate
`~/code/aeneas` repository is needed. Avoid independently pinning Aeneas and
Charon to arbitrary commits: use the pairing tested with cargo-hax 0.4.2.

The declarative selection lives at
`rust/crates/transcrypt-v3-core/hax.toml`. Hax generates the Lean project at
`rust/proofs/aeneas/generated/V3Core/lean/`, inside the Rust workspace
(as required by hax 0.4.2), and excluded from Git. The accompanying
`PROVENANCE.txt` records the Rust source hash, scenario hash, managed tool
versions, and generated sources. The ordinary `proofs/lean` project remains
independent of Aeneas, with its own toolchain.

## Strict proof boundary

`build-v3-generated.sh` refuses missing/empty extraction modules and admitted
(`sorry`, `admit`, `axiom`) generated or external-model Lean declarations. It
requires the generated root to import `V3Wire.Extraction`, then runs Lake on
that module. If the toolchain produces external model templates containing
holes, the build stops: those models need explicit, reviewed contracts.

The independent Lean proofs (`V3WireCodec`) and generated Lean functions must
still be connected by real refinement theorems. Cryptographic library
correctness, Argon2id and AES-SIV security, runtime filesystem effects, and
Git index transitions are **separate** obligations. Do not treat translation
or a successful Lake build as a formally verified end-to-end product.

## Script regression tests

```bash
bash proofs/aeneas/tests/test_v3_bridge.sh
```

This validates extraction/build script behavior using a stub cargo-hax + Lake
binary, **not** the real translator. The actual acceptance commands are the
two scripts above on a machine with Rust and Lean.

Previous `translate-policy.sh` and `translate-legacy-core.sh` entrypoints are
historical and not part of the secure-first v3 acceptance gate.

References: [hax Lean quickstart](https://pereq.dev/hax/manual/lean/quick_start/),
[hax tool management](https://pereq.dev/hax/manual/tools/), and
[Aeneas upstream](https://github.com/AeneasVerif/aeneas).
