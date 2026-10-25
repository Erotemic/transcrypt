# Formal verification ledger — production v3 codec

**Reconciled 2026-10-24:** The user confirmed the tracked Lean/Aeneas build
works and pushed it to `work/m2-nul-safe-path-enumeration`. The three
constant/disjointness theorems are compiled; no encoder/decoder behavior has
yet been proved. For the active cross-component roadmap and exact criteria,
see [`docs/verification/V3-ROADMAP.md`](../../../docs/verification/V3-ROADMAP.md)
and [`V3-PROOF-COVERAGE.md`](../../../docs/verification/V3-PROOF-COVERAGE.md).

| Obligation | Status | Evidence / boundary |
| --- | --- | --- |
| Aeneas translates the four production fixed-width functions | Translated | Checked-in `V3Wire/Extraction/Funs.lean`, pinned toolchain and exact source digests |
| Lean imports actual generated function definitions | Implemented | `V3Wire/Extraction.lean` imported by `V3Wire.lean` |
| Generated config magic refines independent spec | Compiled theorem (user-verified) | `V3Wire/Verification/Refinement.lean` |
| Generated file magic refines independent spec | Compiled theorem (user-verified) | Same |
| Generated formats are disjoint | Compiled theorem (user-verified) | Same |
| Generated config encoder builds exact magic/salt/tag | Open | Requires `encode_config_*` RustM loop invariant |
| Generated config decoder accepts exactly correct 55-byte records | Open | Requires loop termination/bounds and error proof |
| Generated file-header encoder/decoder exactly match spec | Open | Requires `encode_file_header_*` and `decode_file_header_exact_*` proofs |
| Public Rust slice parsers enforce truncation and length | Open | Not among the current four extracted functions |
| AES-SIV and Argon2id crypto | External security assumption | In-process audited implementations/cryptographic assumptions, not v3 wire-codec proofs |
| Git and socket lifecycle | Open | Requires an effect/state transition refinement |

No axiom dumps or routine theorem check inventories are part of normal builds.

### Focused codec loop-body workbench — pending Lean compilation

`V3Wire/Verification/CodecSteps.lean` contains three candidate WP
specifications naming the actual extracted Rust magic-writing, ID-writing,
and ID-decoding loop bodies. These are *per-iteration* claims, not complete
22-byte encoding/decoding refinement. They are intentionally not imported
into the normal `V3Wire.lean` until the following gate passes:

```
bash proofs/aeneas/build-v3-codec-steps.sh
```

Do not upgrade this row to compiled or change W-04/W-05 to PROVED merely
because the new file exists. After the focused build, prove whole-loop
correctness, then the top-level generated encoder and decoder.
