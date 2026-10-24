# Source-derived SMT proof bridge

The `proofs/smt` runners now consume expressions read **from actual Rust
functions** in `rust/crates/transcrypt-protocol/src/base64_bits.rs` and
`rust/crates/transcrypt-policy/src/lib.rs`. They generate an ephemeral
`rust_source_model.h` and compile it into the Z3 checks.

This replaces the former manually transcribed expressions and static source
hashes. A Rust source change automatically produces a different SMT term, or
fails if the restricted reader cannot understand the change.

## Proof commands

```sh
python3 -m unittest discover -s proofs/sourcecheck -p 'test_*.py' -v
bash proofs/smt/run-base64-proof.sh
bash proofs/smt/run-policy-proof.sh
```

Proof and test dependencies: `python3`, a C compiler, and `libz3-dev`.
None is required by the shipped Bash Transcrypt tool. If only a versioned
`libz3.so.4` is installed, set `LIBZ3` to its full path for these commands.

## What the reader accepts

This is a **closed, checked subset**, not a Rust parser:

- Precisely the named `pub fn` or `pub(crate) fn` source functions.
- Arguments of type `bool`, `u8`, or `[u8; 4]`, as specified by the bridge.
- One pure Boolean expression using `&&`, `||`, `!`, or one fixed-size
  `u8` array expression using `&`, `|`, constant shifts, integer literals,
  and fixed array indexing.
- No closures, loops, branches, method calls, macros, `unsafe`, mutable
  state, statements, implicit casts, or unsupported syntax.

Both sides of the expressions are pure; Boolean short-circuit order has no
observational effects in this subset. All byte shifts and bitwise operators
use eight-bit bit-vector semantics, with literal shift amounts below eight.

The test suite also changes the real Rust expressions in temporary copies,
then confirms that Z3 returns a **counterexample** for the changed Base64 or
policy behavior. Separately, it checks the entire 144-state combined Boolean
input space directly from the parsed source.

## Trust boundary

The source reader and its model-generation rules are trusted. The Z3 proof
checks its output, not Rust compiler semantics. The Rust-to-SMT translation
has not been formally verified, and the proofs do not establish correctness
of Git/crypto adapters or the full Base64 decoder. The genuine
Charon/Aeneas-to-Lean refinement remains a separate, mandatory goal.

We intentionally keep the independent specifications inside the C proof
harnesses, not in the Rust expression reader. The reader must **not** choose
its specification by copying the Rust expressions under test.

The earlier `proofs/smt/*-source.sha256` pin files remain as historical
provenance but are no longer a build gate: direct extraction means the source
expressions are retranslated and rechecked on every proof run.
