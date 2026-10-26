# Transcrypt v3: active product and verification roadmap

**Intent updated 2026-10-25; implementation checkpoint: the product-charter campaign (P0–P4 done).** This is
the active plan for the Rust v3 product on
`work/m2-nul-safe-path-enumeration`. The [maintainer product charter]
(V3-PRODUCT-CHARTER.md) governs goals, non-goals, trusted boundaries and
usability tradeoffs; this roadmap tracks completion **without declaring the
campaign finished**.
The older [08 roadmap](08-roadmap-and-pr-plan.md) describes a broader,
historical upstream dual-implementation program. The **one-time legacy
migration** is now an explicit product goal here (P4), not something deferred
merely because the earlier Bash parity plan is historical.

**North star:** selected plaintext files behave like normal files in an
unlocked checkout, while their corresponding public Git objects contain
correct deterministic authenticated v3 ciphertext. Users select arbitrary
paths through Git attributes, unlock persistently by default without a
required daemon, and can opt into strict local privacy if desired. Source-
derived Lean theorems constrain the actual Rust core under explicit crypto,
Git, OS and translation assumptions. Legacy Bash-to-v3 *transition* must be
safe; legacy wire interoperability is not required. A future Bash v3 may
implement the same byte contract independently.

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

**Interpretation:** V0–V6 summarize the **existing experimental baseline**;
they do not imply the product now meets the new charter. Further deliverables
are tracked below. Stages are evidence-based, not percentages. A passing
snapshot hash check is not a function proof, and a working Rust test suite
is not an adapter proof.

## First formal-assurance milestone (not a product stopping point)

The first *meaningful verified v3 milestone* was **V3 + the targeted subset
of V4**, under stated assumptions. It has now been reached for the `*.secret`
core. The product campaign continues: generalized selection, credential
storage and adapter changes must extend/refine these guarantees as needed. It does **not** require formalizing OpenSSL,
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

- [x] Third pass:
      - Git never writes plaintext readable by others (H-16; umask-aware
        smudge plus auto-hydrating hooks);
      - hydrate decrypts exactly the authentic records and never touches
        edits (H-17; Lean model re-proved);
      - bounded subprocess output and an incremental, budgeted audit (H-18);
      - `doctor` and the remote-enforcement check (H-19);
      - Git's long-running filter protocol, with pkt-lines decoded by the
        verified core (H-20: 5–17× faster);
      - strict listing parsers found by fuzzing (H-21);
      - confirmed new passphrases (H-22);
      - `rekey` and `uninstall` (H-23);
      - adapter split into modules;
      - the [Bash correspondence](V3-BASH-CORRESPONDENCE.md);
      - merge and diff drivers, conflict-aware hydrate/status (H-24, H-25);
      - linked worktrees and submodules (H-26);
      - stale-agent retirement after a pulled rekey (H-27);
      - idempotent unlock/lock;
      - clean makes new secrets private.

### Product-charter campaign (2026-10-25, after `d8436c6`)

| Track | Goal | Status and evidence |
| --- | --- | --- |
| **P0: real adapter defects** | F-02 rekey symlink write; F-03 `git mv`; F-04 ignored chmod | **Done.** F-02 reproduced with the compiled CLI, fixed by one symlink-refusing repository-file writer; F-03 fixed by the pre-commit rebind (local changes only, no laundering) and keyless checks; F-04 resolved. See [triage](V3-REVIEW-TRIAGE.md) |
| **P1: arbitrary protected paths** | Git `.gitattributes` selection in production and verified core | **Done.** Suffix-free path policy and `parse_attr_record` proved; `protect`/`unprotect`; per-commit policy in `audit`; workflow tests for `.env`, directories, globs, quoted/non-UTF-8 names, executables, nested rules, exclusions |
| **P2: persistent unlock by default** | Stored derived key, no daemon; memory-only agent optional | **Done.** `.git/transcrypt-v3/key` (0600, outside `git config`), stale after a pulled rekey; `--private` keeps the agent; identical ciphertext in both modes (tested) |
| **P3: transparent Git use** | Ordinary operations under ordinary umasks | **Done** for checkout, switch, merge, rebase, diff, stash, restore, rename, worktrees, submodules; private mode keeps its 0600 promise |
| **P4: migration and Bash map** | Recoverable one-time v2-to-v3 conversion | **Done.** `migrate`, tested against the real Bash script; Bash F-01 fixed; [correspondence](V3-BASH-CORRESPONDENCE.md) updated |
| **P5: proof correspondence** | Extend source-derived proofs to the new decisions | **Done for the core** (path policy, attribute records, smudge, two-mode index entries, the rebind decision and its inputs from Git's listings, the stored-key load, object replies) and models (attribute loop, smudge, the pre-commit hook end to end: [security argument](V3-SECURITY-ARGUMENT.md)); next: smudge/hydrate/lock inputs and the audit loop |
| **P6: release qualification** | Independent crypto/adapter review | **Not complete** (R-01) |

### Next milestones, ranked by expected value

1. Continued adversarial agent review of each change; the external human
   review (R-01) comes last, once everything else is done.
2. Done: the rebind decision is the verified `seal_action`, and its inputs are verified functions of Git's listings (`hook_repairs_only_local_changes`).
3. A hint for cross-branch rename conflicts (Git cannot pair path-bound records; documented limitation).
4. Done: A4 narrowing for selection (`parse_listing_attrs`), the stored-key load (`stored_key_state`) and object replies; the end-to-end hook statement names the remaining contracts (A19–A23). Next: an `ls-tree` record parser, the audit's per-commit loop, the smudge/hydrate inputs.
5. Done: private-agent idle timeout (`unlock --private --timeout=15m`).

**Parallel optional tracks:** server/CI audits for organizations requiring
remote policy enforcement; session-only credential/strict-local-privacy mode;
Git-platform portability and performance; possible independently written Bash
v3 once its crypto/dependency feasibility is resolved. None is allowed to
compromise the main Rust product promise or silently weaken v3 authentication.

**Legacy finding F-01 was real and is fixed in the Bash script** (decrypt
and salt check instead of the prefix); users of existing installs should run
`transcrypt --upgrade` and audit older history. This is not a reason to
teach verified v3 to decrypt legacy CBC.

## Scope discipline and risk decisions

- **Do not implement legacy-v2 features in formally verified v3.** Existing
  v2 security/regression work is maintenance, not a v3 completion gate.
- **Do not require full Bash v3 to preserve the achieved Rust V3/V4 proofs.**
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

**For the next worker:** read [V3-PRODUCT-CHARTER](V3-PRODUCT-CHARTER.md),
[V3-REVIEW-TRIAGE](V3-REVIEW-TRIAGE.md),
[V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md),
[V3-HANDOFF](V3-HANDOFF.md), the exact
[experimental wire spec](specs/V3-AUTHENTICATED-P0.md), the real
[Lean refinement module](../../proofs/aeneas/v3/V3Wire/Verification/Refinement.lean),
and [tracked proof status](../../proofs/aeneas/v3/PROOF-STATUS.md).
