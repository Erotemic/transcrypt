# Charon/Aeneas extraction (not yet executed)

`translate-policy.sh` takes the **real** `transcrypt-policy` Rust crate and
asks Charon to emit LLBC, then Aeneas to generate Lean definitions. It refuses
to generate output if the tools are missing. Do not use source-style retyped
Lean implementations as substitutes for generated functions.

Install a compatible pinned toolchain first, including the Aeneas Lean
library and the Lean release required by that Aeneas backend. Official
references: [Aeneas README](https://github.com/AeneasVerif/aeneas) and
[getting started](https://github.com/AeneasVerif/aeneas/blob/main/documentation/getting-started.md).

Then from the repository root:

```bash
bash proofs/aeneas/translate-policy.sh
```

The resulting `generated/PROVENANCE.txt` records the Rust source and LLBC
hashes and installed tool versions. This file and the LLBC are **not**
checked into the initial overlay: extraction was not possible in this
container, which lacks Rust, Lean, Charon and Aeneas toolchains. Do not claim
T-07/T-08/T-09 as *proved of actual Rust* until the generated functions are
compiled and refinement theorems target them explicitly. See the independent
`proofs/lean/Transcrypt/PolicyGates.lean` model and the currently checked Z3
Boolean obligations.

## Current long-term target: actual legacy v2 core

`bash proofs/aeneas/translate-legacy-core.sh` translates the independent
`no_std` `transcrypt-legacy-core` crate **used by the shipped Rust filter**.
It contains the byte-level `legacy_hmac_key`, `legacy_salt_from_digest`,
`valid_context_name`, and legacy discrimination functions. This is preferred
over further manually maintained SMT correspondence layers.

The independent protocol is
`docs/verification/specs/LEGACY-V2-INTEROPERABILITY.md`. Once translation
works with pinned compatible tools, write a Lean refinement theorem for the
**generated** functions, stating the byte-level semantics and all external
crypto/Git/OS assumptions. Generating a `.lean` file is not a proof; adapter
functions and crypto primitives require separate contracts.
