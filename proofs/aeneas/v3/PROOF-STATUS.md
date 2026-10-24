# Formal verification ledger — production v3 codec

| Obligation | Status | Evidence / boundary |
| --- | --- | --- |
| Aeneas translates the four production fixed-width functions | Translated | Checked-in `V3Wire/Extraction/Funs.lean`, pinned toolchain and exact source digests |
| Lean imports actual generated function definitions | Implemented | `V3Wire/Extraction.lean` imported by `V3Wire.lean` |
| Generated config magic refines independent spec | Theorem authored (compile gate required) | `V3Wire/Verification/Refinement.lean` |
| Generated file magic refines independent spec | Theorem authored (compile gate required) | Same |
| Generated formats are disjoint | Theorem authored (compile gate required) | Same |
| Generated config encoder builds exact magic/salt/tag | Open | Requires `encode_config_*` RustM loop invariant |
| Generated config decoder accepts exactly correct 55-byte records | Open | Requires loop termination/bounds and error proof |
| Generated file-header encoder/decoder exactly match spec | Open | Requires `encode_file_header_*` and `decode_file_header_exact_*` proofs |
| Public Rust slice parsers enforce truncation and length | Open | Not among the current four extracted functions |
| AES-SIV and Argon2id crypto | External security assumption | In-process audited implementations/cryptographic assumptions, not v3 wire-codec proofs |
| Git and socket lifecycle | Open | Requires an effect/state transition refinement |

No axiom dumps or routine theorem check inventories are part of normal builds.
