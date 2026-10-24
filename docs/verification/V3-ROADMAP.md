# Transcrypt v3: active roadmap and stopping criteria

**Active as of 2026-10-24.** This is the primary execution plan for the
secure-first Rust v3 proof of concept on `work/m2-nul-safe-path-enumeration`.
The older [08 roadmap](08-roadmap-and-pr-plan.md) covers the *larger upstream
Bash/Rust and legacy-migration campaign*, not the critical path here.

**North star:** one minimal, deterministic, authenticated v3 format; a usable
Rust implementation covering the full initialize/encrypt/commit/clone/unlock/
hydrate/lock lifecycle; and *real Charon/Aeneas-to-Lean refinement proofs* of
security-relevant production Rust logic against a separately authored spec.
Eventually implement/review the same v3 protocol in standalone Bash, but do
not hold up the Rust proof of concept to achieve full legacy CLI parity.

This is an **experimental security design**, not a production security
certification. The exact bytes and threat assumptions live in the
[normative candidate](specs/V3-AUTHENTICATED-P0.md). An independently
implemented test vector is evidence of conformance, not a cryptographic
security proof. See [proof coverage](V3-PROOF-COVERAGE.md) for precisely
what is and is not established.

## At a glance

| Stage | Result and definition of done | Current status | Critical path? |
| --- | --- | --- | --- |
| V0 — narrow format | One suite (Argon2id + AES-256-CMAC-SIV), exact metadata/record bytes, path AAD, explicit failure/rename behavior and independent vectors | **Implemented as experimental candidate**; external review/freeze outstanding | Yes, freeze before release |
| V1 — Rust lifecycle | `init`, `unlock`, `clean`, `smudge`, `verify-index`, `hydrate`, `lock` operate on real Git repos; negative tests for tampering, incorrect password and stage divergence | **Implemented and tested**; user confirmed latest Rust build/fix works | Achieved for POC |
| V2 — source-derived Lean | Pin actual Rust codec source, translate through Charon/Aeneas, commit generated definitions, reproduce exact output and compile in Lean | **Achieved**; snapshot and initial constant theorems compile; CI gates present | Achieved |
| V3 — functional refinement | The *actual generated* config and file-header encoders/decoders match the independent Lean codec specification on success and errors; public slice-length checks covered | **Open**; only extracted magic/version claims proved | **Next** |
| V4 — authenticated-operation contracts | Production Rust calls a small pure core of decisions for config/key/path/index/authorization; that core is translated and proved to prevent plaintext release or staging outside stated preconditions; crypto treated as an explicit trusted primitive | **Open**; adapters and cryptographic-library behavior not verified | Yes for meaningful formal claims |
| V5 — lifecycle/failure assurance | Real Git/FS/agent tests cover malicious paths, dirty/staged conflicts, interruptions, recovery and cross-path transplants; remaining transactions either hardened or explicitly declared unsupported | **Partial**; substantial happy/negative-path tests, no full multi-file crash transaction | Yes for credible POC / release gate |
| V6 — freeze, review, distribution | Crypto/OS/Git threat review, reproducible tests on advertised platforms, version/profile compatibility decision, honest security and proof claims | **Open** | Required before security-sensitive release |
| V7 — Bash v3 conformance | Bash implements exactly the approved v3 wire/profile; independently test same vectors and lifecycle semantics, with no new Bash runtime dependency unless explicitly renegotiated | **Deferred** | No, for Rust-first POC |

**Interpretation:** stages are deliverable-based, not percentages. A passing
snapshot hash check is not V3. Passing `lake build` of magic constants is not
V3. A working Rust test suite is not proof of V4/V5.

## Smallest valuable formalization — a defined stopping point

The first *meaningful verified v3 milestone* is **V3 + the targeted subset of
V4**, under stated assumptions. It does **not** require formalizing OpenSSL,
RustCrypto internals, Git, the kernel, or arbitrary filesystem scheduling.

1. **Wire refinement (V3):** establish theorem statements about the actual
   `transcrypt_v3_core` Aeneas-generated functions, not a separate Rust-like
   model. Match all 55-byte config and 22-byte header fields, bounds,
   version/magic rejection, and complete-input length gates. Where Aeneas
   yields `RustM`, prove its success/error semantics with appropriate loop
   invariants. Follow the independent spec in
   `proofs/lean/Transcrypt/V3WireCodec.lean`.
2. **Security-decision refinement (V4):** carve only the *decisions the running
   v3 adapter uses* into a small `no_std` Rust seam: canonical path bytes,
   config binding, authenticated-success gating, protected staged-file mode,
   and whether plaintext may be emitted/persisted. Aeneas-extract and prove
   these against independent preconditions. Do not revive an unused policy
   proof crate and count it as product coverage.
3. **Explicit trusted boundary:** treat Argon2id, AES-SIV, entropy source,
   socket/FD permissions, Git object reads, and atomic OS operations as
   external contracts, with tested preconditions and documented limitations.
   A theorem about the pure core yields only *conditional* guarantees about
   the executable. The wider release review remains necessary.

**Allowed claim at this stopping point:** "The production Rust v3 wire and
specified security-decision functions are machine-checked against an
independent specification, assuming the documented cryptographic and Git/OS
adapter contracts." **Disallowed claim:** "Transcrypt v3 is fully formally
verified" or "cryptographic security has been proved from first principles."

## Immediate work sequence (prefer sequential, vertical slices)

### Next: V3 — proof of actual generated codec

- [ ] First choose the smallest generated loop, preferably
      `encode_file_header`, and state a theorem about its *returned bytes*.
      It must quantify over arbitrary valid config IDs, not only fixed magic.
- [ ] Establish a reusable Aeneas array/`RustM` correspondence lemma. Reuse
      that lemma for `encode_config` and each decoder; do not build separate
      near-duplicate proof frameworks.
- [ ] Prove decoder acceptance/rejection and the exact slice-parser length
      boundary. If an Aeneas loop is intractable, refactor the **actual Rust
      production function** to simpler safe-Rust operations, rerun Rust tests,
      regenerate the tracked snapshot, and prove the new generated code.
- [ ] Build with `bash proofs/aeneas/build-v3-tracked.sh` and keep CI's
      regeneration gate matching the exact source. Update
      `proofs/aeneas/v3/PROOF-STATUS.md` with theorem names and coverage.

**V3 acceptance:** Lean theorem(s) use the generated `encode_*/decode_*`
functions in their propositions; all four core functions have full-field and
failure behavior proved under an explicit representation mapping; the
production public slice boundaries are handled (by proof or a justified
separate tested-contract boundary). Neither self-equality nor a theorem
only about `CONFIG_MAGIC`/`FILE_MAGIC` meets this gate.

### After V3: V4 → V5 → V6

- V4: move any essential gating currently embedded in effectful Rust into
  the *invoked* pure Rust core; prove the small resulting functions; keep
  Argon2id/AES-SIV as contract boundaries. Avoid proof work on unrelated v2
  Base64, old policy prototypes, migration and CLI parity.
- V5: target safety-critical state transitions, especially index-versus-HEAD,
  partial hydration, crash during multi-file `lock`, symlink/race exposure,
  agent lifetime, and staged ciphertext substitution. Use adversarial real-
  Git/fault-injection tests; only formalize transition plans if they control
  actual effects. A local pre-commit hook is not a remote trust boundary.
- V6: review the cryptographic dependency and parameters, equality leakage,
  key handling, same-UID socket access, malicious Git checkout behavior, and
  format discriminator. Keep rollback of old valid Git history an explicit
  non-goal unless new trusted freshness state is introduced.

## Scope discipline and risk decisions

- **Do not implement legacy-v2 features in formally verified v3.** Existing
  v2 security/regression work is maintenance, not a v3 completion gate.
- **Do not require full Bash v3 or legacy migration to finish Rust-first V3/V4.**
  Bash portability is an independent follow-on track under the old 08 plan.
  The CLI-only OpenSSL feasibility study found no straightforward safe
  AES-SIV implementation under the existing Bash dependency policy: do not
  weaken the Rust protocol to accommodate it. Either renegotiate the Bash
  runtime contract, obtain a reviewed Bash-feasible implementation, or ship
  a Rust-only secure suite until Bash conformance is viable.
- **No extra SMT milestones:** source-independent solver exercises are not a
  substitute for the Rust-generated Lean correspondence. Keep useful existing
  evidence without expanding it unless it supports the actual Rust proof.
- **Profile stability:** the path-bound associated-data format intentionally
  superseded an earlier experimental v3 variant without changing the 22-byte
  header. Before public release, freeze the precise profile/version and
  determine how previously issued experimental records are identified and
  handled; **never silently reinterpret released ciphertext**.
- **Deterministic leakage:** the same plaintext at the same path in the same
  repo yields the same ciphertext; renames require re-encryption. Old valid
  snapshots can be replayed. These are documented protocol limits.
- **Proof overhead:** after two unproductive attempts at a generated-loop
  proof, prefer one production Rust simplification and re-extraction to a
  growing custom Lean framework. Retain precise tests and data formats.

## Working commands and source of truth

From the repository root:

```bash
cd ~/code/transcrypt
cd rust && cargo test --offline --workspace && cd ..
python3 tests/v3/reference/check_vectors.py -v
python3 proofs/aeneas/v3_snapshot.py verify
bash proofs/aeneas/build-v3-tracked.sh
```

When the verified Rust codec or its hax scenario changes, regenerate and
review rather than editing extracted Lean:

```bash
cd ~/code/transcrypt
bash proofs/aeneas/translate-v3-core.sh
python3 proofs/aeneas/v3_snapshot.py compare
# Only after reviewing intended source, Lean, assumptions, and toolchain changes:
python3 proofs/aeneas/v3_snapshot.py refresh
bash proofs/aeneas/build-v3-tracked.sh
```

The checked-in extraction is under `proofs/aeneas/v3/`; never commit `.lake/`
or `rust/proofs/aeneas/generated/`. The latest actual build/compile reports
from the user's machine take precedence over stale file commentary.

**For the next worker:** read [V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md),
[V3-HANDOFF](V3-HANDOFF.md), the exact
[experimental wire spec](specs/V3-AUTHENTICATED-P0.md), the real
[Lean refinement module](../../proofs/aeneas/v3/V3Wire/Verification/Refinement.lean),
and [tracked proof status](../../proofs/aeneas/v3/PROOF-STATUS.md).
