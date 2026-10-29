# Version-controlled Aeneas extraction of the production Transcrypt v3 codec

This directory contains the **real**, non-handwritten Charon/Aeneas output
produced from `rust/crates/transcrypt-v3-core/src/lib.rs` by the pinned
`cargo-hax 0.4.2` Lean backend. The generated `V3Wire/Extraction*.lean`,
`V3Wire/Assumptions/FunsExternal.lean`, pinned `lakefile.toml`, `lean-toolchain`,
and `lake-manifest.json` are tracked. The exact bytes and production Rust
sources are bound by `SNAPSHOT.json`. No `.lake` dependencies or compiled files
are tracked.

The one authoritative independent specification remains in
`proofs/lean/Transcrypt/{V3Wire,V3WireCodec,V3Policy}.lean`. The build script
stages byte-for-byte copies as *ignored* build inputs under `Transcrypt/`; it
cannot silently fork the specification.

## Build (no Charon regeneration required)

```bash
cd ~/code/transcrypt
python3 -m unittest discover -s proofs/aeneas/tests -p 'test_v3_snapshot.py' -v
bash proofs/aeneas/build-v3-tracked.sh
```

The tracked `V3Wire` library imports the production extraction and the
hand-written proof modules under `V3Wire/Verification/`. Compilation is a
real Lean kernel gate. What those modules prove, function by function, is the
ledger [`PROOF-STATUS.md`](PROOF-STATUS.md): the complete result of every
core function (all bytes, every error outcome, no panic or divergence)
against the independent specification, protocol results relative to the
explicit primitive contract `Realizes`, and end-to-end statements about Lean
models of the adapter. `bash proofs/aeneas/check-v3-axioms.sh` audits the
axioms of every theorem the ledger names (`audit/Axioms.lean`).

They do **not** verify Argon2id, AES-SIV, SHA-256, Git, the credential
agent's IPC, or filesystem transactions; see
[`V3-ASSUMPTIONS.md`](../../../docs/verification/V3-ASSUMPTIONS.md).

## Update when verified Rust changes

```bash
cd ~/code/transcrypt
bash proofs/aeneas/translate-v3-core.sh
python3 proofs/aeneas/v3_snapshot.py compare
```

The compare step is expected to **fail** when the production Rust code or
extracted Lean definitions actually change. The developer then intentionally
refreshes the reviewed snapshot:

```bash
python3 proofs/aeneas/v3_snapshot.py refresh
bash proofs/aeneas/build-v3-tracked.sh
```

`refresh` never adopts new external assumptions, Lean toolchain pins, or
changes to the generated dependency manifest automatically. Those require an
explicit reviewed edit. CI performs a source-hash gate every run; the dedicated
regeneration CI job compares with the real managed Charon/Aeneas output.

## Provenance and proof obligations

- Source Rust: `rust/crates/transcrypt-v3-core/src/lib.rs`
- Exact hax scenario: `rust/crates/transcrypt-v3-core/hax.toml`
- Translator: cargo-hax 0.4.2 / Charon `nightly-2026.09.02` /
  Aeneas `build-183e4f0`
- Lean: `leanprover/lean4:v4.31.0`, hax Lean library `v0.3.30`
- Proofs: `V3Wire/Verification/*.lean` (shared lemmas in `Basic.lean`,
  production constants in `Refinement.lean`); status in `PROOF-STATUS.md`.

Do not count `V3Wire/Extraction.lean` compilation, a check of `SNAPSHOT.json`,
or the mere presence of Aeneas-generated files as a full functional proof.
