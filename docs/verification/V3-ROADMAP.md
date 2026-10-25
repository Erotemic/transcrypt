# Transcrypt v3: active roadmap and stopping criteria

**Active as of 2026-10-24; statuses reconciled 2026-10-25.** This is the primary execution plan for the
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
| V0 — narrow format | One suite (Argon2id + AES-256-CMAC-SIV), exact metadata/record bytes, path AAD, explicit failure/rename behavior and independent vectors | **Frozen as v3 profile 1** (decision in [V3-SECURITY-REVIEW](V3-SECURITY-REVIEW.md)); external review outstanding | Done for POC |
| V1 — Rust lifecycle | `init`, `unlock`, `clean`, `smudge`, `verify-index`, `hydrate`, `lock` (+ `status`, `help`) on real Git repos; negative tests | **Achieved** | Done |
| V2 — source-derived Lean | Pin actual Rust core, translate through Charon/Aeneas, commit generated definitions, compile in Lean | **Achieved**; regeneration reproduced byte-for-byte locally and in CI | Done |
| V3 — functional refinement | All four codec functions and the public slice parsers, full-field and failure behavior | **Achieved** (`Codec.lean`) | Done |
| V4 — authenticated-operation contracts | Production Rust calls a pure core for every decision; the core is translated and proved; crypto is an explicit contract | **Achieved**: the core owns seal/open/authenticate/authorize/attribute/hydrate/lock decisions (`Protocol.lean`, `Bytes.lean`, `Path.lean`) relative to `Realizes` | Done |
| V5 — lifecycle/failure assurance | Malicious paths, staged conflicts, interruptions, recovery, transplants; transactions hardened or declared | **Achieved for the stated threat model**: Lean lifecycle models (`Lifecycle.lean`), adversarial suite, private staging, dirfd resolution, resumable lock/hydrate; multi-file atomicity is explicitly not claimed | Done |
| V6 — freeze, review, distribution | Threat review, reproducible tests, profile decision, honest claims | **Internal review done** ([V3-SECURITY-REVIEW](V3-SECURITY-REVIEW.md), [V3-ASSUMPTIONS](V3-ASSUMPTIONS.md), [user guide](V3-USER-GUIDE.md)); Linux+macOS CI; **external review (R-01) outstanding** | Release blocker |
| V7 — Bash v3 conformance | Bash implements exactly the approved v3 wire/profile | **Deferred** by policy: no reviewed Bash-feasible AES-SIV under the current dependency contract | No |

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

## Work sequence

### Completed (2026-10-25)

- [x] Whole-function refinement of every codec function, including the
      public slice parsers (V3).
- [x] Every security decision moved into the extracted core, with the
      adapter reduced to primitives and effects, and each decision proved
      against the independent spec `V3Policy.lean` (V4).
- [x] Lifecycle sequencing proved in Lean models; adversarial real-Git
      suite; crash-safe private staging; dirfd resolution; agent hardening
      (V5).
- [x] Internal security review, trust-ordered assumption register, user
      guide, axiom audit and CI gates (V6, internal part).
- [x] Security-hardening campaign
      ([V3-SECURITY-REVIEW §5](V3-SECURITY-REVIEW.md#5-hardening-campaign-second-pass-2026-10-25)):
      - fixed a reproducible plaintext-staging bug in hydration (H-1);
      - all Git objects are now read by verified object id from one snapshot
        (H-2);
      - added a keyless `audit` command and a `pre-push` hook (H-3);
      - wiped Argon2 memory and moved AES-SIV in place (H-4, H-5);
      - added the differential crypto corpus (H-6);
      - stamp-checked replacement and an operation lock (H-7);
      - peer-UID checks (H-8);
      - made locked checkouts usable without weakening the plaintext gate
        (H-9);
      - added SIGKILL fault injection.
      New proved core functions: `is_object_id`, `record_envelope_ok`.

### Remaining, ranked by security value (see [V3-ASSUMPTIONS](V3-ASSUMPTIONS.md#ranked-unresolved-risks))

1. **A13 — server-side enforcement.** Plaintext from checkouts that never
   ran `unlock` is only stopped where `audit` runs. Ship and document a
   CI/pre-receive integration and make it part of the setup.
2. **R-01 — external review** of the construction, `aes-siv`, the
   locked-filter envelope pass-through (A14) and the adapter, using the
   [review package](V3-SECURITY-REVIEW.md#review-package). Release blocker.
3. **A4 — adapter remainder.** Object reads are batched
   (`cat-file --batch`, exact header check); move that check into the proved
   core, adopt Git's long-running filter protocol (one filter process per
   Git command instead of one per file), keep the call-site table current.
4. **A7 — Git versions.** CI covers Git 2.34, 2.43 and Apple Git; extend if
   users report others.
5. **A8/A6 — same-UID** races and agent access are accepted; an optional
   agent idle timeout and an `nlink > 1` warning at lock are cheap
   follow-ups.
6. **A3 — translator trust.** Track Aeneas/hax releases.
7. **V7 — Bash** only after a dependency-policy decision for AES-SIV.

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
