## October 24 follow-up: checked correspondence to source expressions

The SMT runners now generate each modeled Rust expression from the **current
Rust source** using a deliberately restricted parser under
`proofs/sourcecheck/`. Any unrecognized Rust syntax fails the proof run
instead of falling back to a manual model. The independent bit-slice and
Boolean policy specifications remain in the original SMT C drivers.

- **15/15 universal Base64 obligations passed locally**, including direct
  composition of the source-derived Rust splitter/joiner for all `2^24`
  byte triples and all `2^24` sextet quartets, plus canonical tail laws.
- **22/22 universal policy obligations passed locally**, including
  bidirectional source/spec equivalence of all three Boolean gates.
- **6/6 bridge regression tests passed locally**, including negative
  mutation tests which force Z3 to produce SAT counterexamples and an
  independent exhaustive evaluation of all 144 Boolean input combinations.

Commands: `python3 -m unittest discover -s proofs/sourcecheck -p 'test_*.py' -v`,
`bash proofs/smt/run-base64-proof.sh`, `bash proofs/smt/run-policy-proof.sh`.
A versioned libz3 installation requires the `LIBZ3` override documented in
`proofs/sourcecheck/README.md`.

This improves the **correspondence evidence** beyond a pinned SHA plus human
transcription, but it still trusts the small source-subset translator.
It is neither a Charon/Aeneas translation nor a proof of the complete Rust
parser or of authenticated v3 encryption. Compilation of Rust/Lean and
Aeneas-generated refinement remain distinct milestones.

# First checked proof slice: legacy Base64 and pure security gates

Date: 2026-10-24. Baseline: `36f7c5e` plus the preceding staged-index
security overlay. This work neither changes the legacy ciphertext wire format
nor selects the unresolved modern AEAD construction (D-01).

## What is actually checked

`proofs/smt/base64_bitvector.c` uses the Z3 C API and QF_BV, with 8-bit
input bytes and 6-bit Base64 symbols. Each obligation asserts the negation
of a universally quantified claim, then requires an **UNSAT** result. This
is an exact finite-domain proof in the solver's fixed-width logic, not a
bounded *sample* of byte values. Nine claims were discharged with Z3 4.13.3:

1. Every 3-byte input block roundtrips through six-bit symbols (`2^24` inputs).
2. The shift/mask/OR operations from the *production Rust* `split_triple`
   agree with an independently written bit-slice specification.
3. All outputs of that Rust splitter lie in the Base64 sextet range `[0,63]`.
4. Every four-sextet input block roundtrips back to the same symbols
   (`2^24` symbol tuples).
5. The shift/OR operations from the production Rust `join_quartet` agree
   with an independent byte-concatenation specification.
6. One-byte-tail Base64 padding is unique when residual bits are zero.
7. Two-byte-tail Base64 padding is unique when residual bits are zero.
8. Every 1-byte tail roundtrips after zero-fill and removing padding.
9. Every 2-byte tail roundtrips after zero-fill and removing padding.

The functions actually used by the Rust codec live in
`rust-legacy/crates/transcrypt-protocol/src/base64_bits.rs`, and are invoked from
`base64.rs`. The Z3 harness manually models **those exact operations**, but
is not an automatically generated Rust extraction. The proof driver requires
SHA-256 fingerprints for both production files, so it fails closed on later
source drift until the model is re-reviewed. This fingerprint does not prove
translation correspondence; that remains a human review and later Aeneas
refinement obligation.

`proofs/smt/policy_bitvector.c` proves 16 universal Boolean properties of
three pure Rust preflight decision gates in the new `transcrypt-policy`
crate. In particular:

- secure staged-path approval requires staged-or-effective protection,
  a staged regular file, complete public configuration, correct metadata
  binding, and a positive ciphertext authentication result;
- staged protection cannot be hidden by a local `info/attributes` override;
- persistent unlock writes require successful authentication, valid public
  config, safe destination, and unchanged source snapshot;
- migration publication requires authenticated source and destination
  objects, all contexts, complete target config, stable source, and rollback.

For these properties, `authenticated`, `metadata_matches`, and similar
inputs are **uninterpreted evidence supplied by trusted callers**. The
proof says exactly what decisions follow when the evidence is true or false.
It does not establish that Git, the operating system, the crypto library,
or Bash supply correct evidence, nor that an adapter implements the plan.
The Rust policy functions are currently prospective and are **not wired
into the legacy Bash CLI**.

## Commands and local results

With a C compiler, SHA-256 utility, and development Z3 library:

```bash
bash proofs/smt/run-base64-proof.sh
bash proofs/smt/run-policy-proof.sh
```

On a Linux host with only a versioned `libz3.so.4` runtime:

```bash
LIBZ3=/usr/lib/x86_64-linux-gnu/libz3.so.4 \
  bash proofs/smt/run-base64-proof.sh
LIBZ3=/usr/lib/x86_64-linux-gnu/libz3.so.4 \
  bash proofs/smt/run-policy-proof.sh
```

Locally observed: Z3 4.13.3; **9/9 Base64** and **16/16 policy** universal
obligations UNSAT, C compiled with `-Wall -Wextra -Werror -pedantic`.
A separate Bats-compatible local runner reported **196/196** v2/v3 shell
tests passing. It is not an official Bats run.

## Lean proof target and status

An independent Lean specification and theorem statements with tactic proofs
(no `sorry` or `axiom`) have been added under `proofs/lean/`. The new GitHub
workflow runs the pinned Lean 4.33.0 toolchain and compiles that package.
The development container has neither Lean nor Rust installed, and has no
network access to install either. **Lean compilation and Rust compilation
were not performed locally**; the Lean file is not claimed as a completed
Lean-kernel proof until the dedicated CI job succeeds. The Z3 results above
are real local proof checks, but do not substitute for that Lean gate.

For a machine-checked theorem *about actual Rust*, the next step is to run
Charon/Aeneas on the compiled `transcrypt-policy` crate and the production
base64 bit core and prove refinement to these independent specifications.
Such an Aeneas translation has **not** been generated. Follow the current
[formal-verification roadmap](../05-formal-verification.md); never replace
real generated functions with hand-written lookalikes in proof statements.

## Assumptions and remaining requirements

- Z3's solver and C API are trusted for the local unsatisfiability results.
  The Rust-to-Z3 expression correspondence is a manually reviewed mapping,
  source-pinned but not machine-proved.
- Per-block bit identities and canonical pad bits are not a proof of the
  full Base64 parser (allocation bounds, line breaks, offsets, early return,
  malformed messages, or all arbitrary-length list induction cases).
- The legacy ciphertext format is unauthenticated; nothing here grants it
  authenticity, confidentiality against password attacks, or secure deletion.
- The operational proof is conditional on correctly classified staged paths,
  key material, public config, crypto authentication, and atomic adapter
  effects. A local Git hook can be bypassed.
- The final deterministic authenticated v3 wire format remains blocked on
  D-01/D-02 decisions and independent crypto review.

## Aeneas handoff

A proof-generation entrypoint now exists at
`proofs/aeneas/translate-policy.sh`. Once compatible Charon/Aeneas/Rust
versions are pinned and installed, it extracts LLBC from the *actual*
`transcrypt-policy` crate and generates Lean source with a provenance
manifest. This script has **not** been run: the current container refuses
with `Missing cargo`, as intended. Extracted code alone still requires
proof of refinement to the independent Lean model. The absence of a generated
Lean module in this overlay is deliberate, not an implicit verification claim.
