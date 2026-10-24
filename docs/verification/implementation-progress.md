# Implementation progress

**Maintained per the execution procedure in 08-roadmap-and-pr-plan.md. Short
and factual: current milestone, completed changes with evidence, blockers,
next task.**

Baseline: `elasticdog/transcrypt-v3` @ `fcf94da` + planning-docs commit
(`docs/transcrypt-verification-plan`). Active branch:
`work/m2-nul-safe-path-enumeration` (stacks on the docs commit).

## Completed

### M0 — Complete
Planning overlay applied (11 docs + 2 reference docs).

### M2.1 — NUL-safe path enumeration (committed `dc2e3ff`)
- **Defect (in this working tree; audit class A7):** `_list_encrypted_files`
  line-joined the NUL check-attr stream and unquoted with `eval`;
  newline-containing filenames fragmented into bogus paths silently skipped
  by `--list` and the pre-commit hook. Reproduced a plaintext-blob commit
  bypass before the fix.
- **Fix:** NUL-delimited end-to-end stream, no `eval`; consumers
  (`git_pre_commit`, `list_files`, `show_raw_file`) use `read -r -d ''`.
- **Evidence:** `tests/{v2,v3}/test_pathnames.bats` (6 tests each; the two
  pre-commit rejection tests fail before / pass after the fix);
  `bats --jobs 4 tests/v2/ tests/v3/` → 176/176 ok; `shellcheck` clean;
  `shfmt` clean.
- **Limitations (documented):** line-based `--list` display of newline
  names is inherently ambiguous; `--rekey`/`--uninstall`/`force_checkout`
  still consume line-based `git ls-crypt` (M5 follow-up).

### M1 (partial) — D-01/D-02 feasibility evidence (OpenSSL 3.0.13 + 3.5.9)
- **Probe:** `contrib/verification/d02-openssl-cli-probe.sh` (bash+openssl
  only; RFC 7914/RFC 4231/SP 800-38B vectors + pycryptodome-computed
  constants + /proc argv/environ inspection + a section-7 kdf value-
  semantics classifier). All checks pass on 3.0.13 and 3.5.9.
- **Evidence doc:** `docs/verification/reference/d01-d02-feasibility.md`.
  Key results (3.0.13 and 3.5.9):
  - `enc` exposes no SIV/GCM/CCM; `mac` CMAC is broken on both ⇒
    **RFC 5297 AES-SIV is not implementable in the plain 3.0/3.5 CLI**
    (D-01: evidence-backed, not decided). 3.5.9 also disproves the
    "3.1+ adds file-keyed kdf" hypothesis: kdf `pass`/`salt`/`secret`
    values are literal text (only `hexpass:`-style key-name prefixes
    decode).
  - `enc -pbkdf2 -iter N -S <8B> -pass file:|fd:` = PBKDF2-HMAC-SHA256
    with **no secret in argv** (verified byte-exact) — but 3.0+ only
    (D-03/D-09 implications; 8-byte `-S` limit).
  - Raw-key AES-CTR/ECB via `-pass file:|fd:` = documented
    EVP_BytesToKey(SHA-256) expansion, verified byte-exact (D-02).
  - Every CLI keyed-MAC channel (mac/dgst `-macopt hexkey`) puts the key
    in argv (D-02; A6 class).
- **Options paper:** `docs/verification/11-crypto-options-paper.md`
  (A: SIV — recommended, with Bash sub-options A1/A2/A3; B: PRF-as-MAC —
  currently not CLI-feasible; C: October prototype — excluded). Unapproved
  by design; the frozen spec follows the external decision.
- **CI:** `feasibility-probe` job added to
  `.github/workflows/run-bats-core-tests.yml` (same OS matrix) so the
  capability table is collected per supported platform (Gate B).

### M6 (partial) — Rust `transcrypt-protocol` core: legacy v2 parser
(roadmap: M6 may partially proceed once the relevant spec slice is
agreed; the v2 slice is the released format, so this is unblocked)
- **New zero-dependency crate** `rust/crates/transcrypt-protocol`
  (builds offline; layout per 04). Implements `detect_format`,
  `parse_v2`, a strict standard-base64 decoder (RFC 4648 vectors,
  residual-bit checks, CRLF-tolerant line breaks), and `V2Record`
  (salt + ciphertext split) with structured errors.
- **Fail-closed discriminator:** a blob with the v2 base64 prefix that
  fails structural validation is `Invalid`, never demoted to plaintext
  (R-03); empty input is `Plaintext` by the released design.
- **Evidence:** 14 tests — unit (RFC 4648 vectors; strictness; hostile
  1 MB inputs incl. NUL/0xff/repeated-prefix/1 MB LCG data; decoder
  vs encoder agreement) plus a **differential test** that builds real
  v2 blobs with the Bash pipeline's exact openssl commands and checks
  the Rust parser's split against it (salt equality, ciphertext
  decrypts via the Bash pipeline, truncation fails closed).
  `cargo test --offline` and `cargo clippy` clean.
- **Out of scope until D-01:** any v3 grammar, key derivation, or
  decryption (those live in the future crypto adapter; this crate must
  not define the secure format by example).

## Audit findings vs this working tree (per 07)

A1, A2, A4, A5, A8: not present — artifacts of the unreleased `TCRYPT3`
overlay (no v3 config writer, no PBKDF2, no salt-in-config here).
A6: v2 passes the password via child env (`ENC_PASS`), not derived-key
argv; the argv variant is overlay-only. A7: fixed above (newline
enumeration); the magic-only check itself is v2's designed check.
A3: v2 flush/uninstall cache removal exists; full closeout is M5.

Additional observation (candidate finding, not yet classified):
`transcrypt.crypt-dir` (attacker-writable in `.git/config` of a cloned
repo) redirects `save_helper_scripts` `mkdir`/`cp`/`chmod` outside the
git dir; `add_pattern`/`sed_inplace` write through `.gitattributes`
symlinks. Needs a decision on the `crypt-dir` override policy before any
fix (compatibility impact on shared-gitdir workflows).

## Blockers

- M1 freeze: D-01..D-06 are external decisions (crypto review,
  maintainer platform policy). Evidence for D-01/D-02 now covers OpenSSL
  3.0.13 and 3.5.9; **OpenSSL 1.1.x and LibreSSL remain unprobed**
  (the CI `feasibility-probe` job will produce those; record verbatim
  output when it runs). LibreSSL expectations: no `kdf`, no `mac` app,
  no `-pbkdf2`; `enc -pass file:/fd:` + legacy ciphers available —
  confirm, don't assume.
- M3+ (Bash v3 implementation) waits for a D-01 direction decision.
- M6 (Rust) is **partially** unblocked: the legacy v2 parser slice is
  done; the secure-format parser/serializer, policy crate, crypto
  adapter, and interop suite all wait on the frozen v3 spec (M1).

## Next unblocked task

1. Once CI (or any 1.1.x/LibreSSL host) produces probe output, append it
   to `docs/verification/reference/d01-d02-feasibility.md` verbatim.
2. The options paper (11) is ready for the external D-01 decision; when a
   direction is chosen, write the frozen `PROTOCOL-<id>.md` from it, then
   continue M6 in `rust/` (v3 parser/serializer, policy crate) and M3 in
   Bash from that single spec.
3. No further Bash v2 hardening is known in this tree beyond the A7 fix
   (see audit cross-check above); the `crypt-dir`/symlink-redirect
   observations are queued for a maintainer decision before any fix.

## October 24 2026 independent follow-up — staged-index security and Rust interoperability

- **Confirmed bypass 1:** staged `.gitattributes` required encryption but
  the working-tree `.gitattributes` had been edited to omit it; plaintext was
  committed with the original hook. The hook now uses `check-attr --cached`.
- **Confirmed bypass 2:** staged regular plaintext while the worktree path
  was a symlink; the original hook skipped it. Stage-0 index mode is now
  authoritative (`_staged_path_mode`), using literal-path lookup.
- **Failure handling:** index-path enumeration now propagates Git errors
  rather than treating a failed pipe/substitution as an empty list;
  error-path temp files are cleaned even after Bash function locals expire.
- **Portable policy:** local `.git/info/attributes` can override even
  `git check-attr --cached`. The hook now unions the effective local policy
  with an isolated Git-dir view of the staged portable attributes. An
  explicit reproduction committing plaintext with `secret -filter` in
  `.git/info/attributes` is rejected after the fix.
- **Legacy compatibility:** staged symlinks remain allowed; ordinary
  encrypted commits succeed; missing `nproc` uses a single-worker fallback.
  A linked Git worktree also passed a direct staged-hook smoke check.
- **Tests:** 10 new staged-index cases duplicated in the v2/v3 Bats suites
  (20 new test cases). A local Bats-compatible harness exercised the full
  collection; a native `bats` binary was not available in this container.
  The authoritative native Bats CI job must still run.
- **Rust integration test hardening:** removed a predictable /tmp/password-file
  fixture that could follow an attacker-created symlink and overwrite a
  writable file; the test now passes a **public dummy** password through
  `ENC_PASS`, matching the released Bash legacy filter. This is test code,
  not a recommended secure-v3 credential transport.
- **Rust parser correction:** v2 permits OpenSSL cipher modes with arbitrary
  positive ciphertext length, not just AES-CBC block lengths. The Rust crate
  now splits/serializes opaque v2 envelope bytes, rejects trailing Base64
  after padding, and tests CBC/CTR compatibility. This is **not a compiled
  Rust validation in this container** (`cargo`/`rustc` absent); CI remains
  the compilation/test gate. See
  [v2 wire structure](reference/v2-wire-structure.md).
- **Formal status:** no Lean/Aeneas translation or theorem compiled in this
  follow-up. Candidate future proof target is
  `parse_v2(encode_v2(record)) = Ok(record)` for nonempty opaque ciphertext.
- **Still open:** marker-only v2 hook (no authentication), local bypassable
  Git hooks, index-writer concurrency, v3 crypto and format D-01..D-06,
  and all required v3 operational + formal verification milestones.

**Next independently unblocked task:** compile/test the corrected Rust crate
using `cd rust && cargo test --offline`, then translate the pure Base64 and v2
record functions through pinned Charon/Aeneas. Keep any authenticated format
work blocked on the external D-01 decision, and address remaining Git
security obligations separately from legacy interoperability.


## Update — October 24: first solver-checked proof slice and security decision kernel

- **Rust codec:** isolated the actual Base64 per-block `split_triple` and
  `join_quartet` operations in a small pure module used by both encoder and
  decoder; corrected the reported byte/offset for invalid residual bits when
  CR/LF interrupts a padded quartet. No wire-format change intended.
- **Rust policy:** added `transcrypt-policy`, a `no_std`, dependency-free pure
  preflight kernel for protected-stage acceptance, unlock persistence, and
  migration publication. These functions are prospective; adapter wiring
  and evidence validation are not complete.
- **Checked SMT evidence:** Z3 4.13.3 returned UNSAT for 9 universal Base64
  block algebra obligations and 16 universal abstract policy obligations.
  Drivers enforce source-file SHA-256 fingerprints. See
  `reference/m6-formal-bitcore.md` for precise scope and commands.
- **Independent Lean source:** `proofs/lean/` contains first candidate
  `bv_decide` proofs for those bit-vector and Boolean specifications, and
  the CI workflow contains dedicated Lean and SMT jobs. Local Lean/Rust
  toolchains are unavailable; no local compilation of Lean or Rust is
  asserted. The CI jobs are not yet reported as run.
- **Bash regression:** local Bats-compatible runner reported 196/196 cases
  passing after stacking the preceding 13-file staged-index overlay.
  Official Bats remains the CI gate.
- **Next unblocked work:** compile both new Rust crates and focused Lean
  targets in the pinned toolchains, fix any compiler/tactic errors, run
  Charon/Aeneas on the actual bit core and policy functions using the new
  `proofs/aeneas/translate-policy.sh` entrypoint, and establish generated-code
  refinement rather than relying on the manual source-model correspondence. Do not claim T-01, T-07, T-08, T-09 or T-12 complete for
  the whole application based on these smaller obligations alone.


## Update — October 24: source-derived SMT proofs and build hygiene

- `.gitignore` now excludes Lake's `.lake/` at any depth, Lean object files,
  Rust `target/` outputs, local proof-generation files, Python test caches,
  virtual environments, and editor scratch files. The Rust `Cargo.lock` stays
  tracked as a reproducibility input.
- Replaced the manually transcribed Rust-to-SMT expressions with a strict
  source reader (`proofs/sourcecheck/`) that generates Z3 AST declarations
  from the *real* Rust bitcore and policy functions. Unsupported syntax fails
  closed. This is a **trusted subset translation**, not Charon/Aeneas.
- Added direct source-derived full-block and padded-tail identities and
  bidirectional Boolean source/spec equivalence. Locally Z3 discharged
  **15 Base64 + 22 policy = 37 universal SMT obligations**.
- Bridge regression tests **6/6 passed**, including mutations that produced
  SAT counterexamples and an independent exhaustive check over all 144 policy
  Boolean input combinations. CI now runs these tests before the SMT checks.
- No Bash ciphertext functionality changed. The earlier user's Lean header
  correction is included as part of the cumulative working baseline but
  the Lean toolchain, Rust toolchain and Aeneas are unavailable in the
  current container. The user's prior Lean build success is preserved.
- **Next unblocked task:** compile/test Rust and Lean with installed tools,
  then extract actual `transcrypt-policy` functions through compatible,
  revision-pinned Charon/Aeneas and prove refinement against
  `Transcrypt.PolicyGates`. Do not claim SMT subset proofs establish that
  refinement.

## Next long-term implementation slice — executable Rust parity with Bash v2

- Stop extending standalone SMT source models. The SMT proof infrastructure
  remains available for opt-in experiments but is no longer a default CI gate
  or a roadmap milestone. The target is Rust application parity + actual
  Charon/Aeneas refinement under a shared specification.
- Added independent legacy-v2 byte-exact specification at
  `specs/LEGACY-V2-INTEROPERABILITY.md`: salt derivation, OpenSSL envelope,
  filter decision/failure behavior, public vectors, and Bash/Rust review map.
- Added `no_std` Rust `transcrypt-legacy-core` to hold real pure logic that
  the Rust executable calls. Added `transcrypt-legacy` CLI as a *legacy-only*
  Git clean/smudge/textconv adapter; uses Git local config and OpenSSL CLI for
  v2. Defaults/named contexts, filenames as bytes (on Unix), binary content,
  and OpenSSL 1.1/3 header normalization are covered by new integration tests.
- Changed Bash clean to honor Git stdin instead of worktree file size; buffered
  v2 smudge/textconv decryption before emitting plaintext to prevent partial
  decryption output on error; explicitly reject provisional v3 records rather
  than downgrading to the v2 filter. Kept existing v2 ciphertext bytes.
- Added Bats regression cases, a standalone Bash contract runner, and Rust
  integration tests that compare actual Git-index blobs and Bash ciphertext to
  Rust output. The Rust workspace still needs native `cargo test --offline`
  on a Rust-equipped host; this container has no `cargo`/`rustc`/Aeneas.
- Added Aeneas translation entrypoint for `transcrypt-legacy-core` **without
  claiming translation or refinement completed**. The external OpenSSL/Git
  adapters remain trusted until separately analyzed/verified.

**Still missing for the north star:** Rust implementation of the rest of
Bash's operational CLI, safe v3 crypto + shared approved wire format,
transactional Git adapters, interoperable secure Bats/Rust tests, compiled
Charon/Aeneas refinement theorems, and independent cryptographic review.
Next work: run the Rust integration suite, address any real compiler or
OpenSSL/LibreSSL disagreements, then expand the Rust Git planning/transaction
layer against `03-git-state-machine.md`. Do not add another manually
transcribed solver proof instead of implementing runtime behavior.

## October 24 — Secure-first Rust v3 lifecycle POC (this overlay)

- Added `transcrypt-v3-core`: pure, `no_std`, fixed-length, strictly versioned
  config and file header encoding/parsing; new Aeneas translation target.
- Added `transcrypt-v3`: Argon2id v19 64 MiB/3 passes and AES-256-CMAC-SIV,
  deterministic authenticated file records, authenticated public config,
  separate Unix-only Git init/unlock, required clean/smudge, staged-object
  verification hook, clone hydrate, and lock that flushes tracked plaintext.
- Added independent OpenSSL-backed Python AES-SIV and argon2-cffi vectors,
  Rust vector tests and full Git lifecycle test including negative cases.
- Added independent Lean abstract wire model (`V3Wire.lean`) with structural
  theorem statements; **not a proof of Aeneas-generated Rust**.
- Local evidence: `python3 tests/v3/reference/check_vectors.py -v` passes
  (2 tests); shell syntax and Cargo TOML were checked.
- **Not validated here:** Cargo compilation/integration and Lean builds: this
  model container has neither Rust nor Lean and cannot download toolchains.
  RustCrypto AES-SIV explicitly warns it has not been independently audited.
- **Known prototype limitations:** derived key stored in local `.git` while
  unlocked, incomplete atomic recovery, no full lifecycle proof, unbounded
  Git index object collection in the adapter, no Bash v3 implementation,
  no cross-platform validation, no rekey/migration or rollback protection.
  Formal release claims are blocked until these are addressed or clearly
  scoped and reviewed.

**Next task:** obtain Cargo compilation results, correct compiler/integration
failures, run Charon/Aeneas on `transcrypt-v3-core`, and prove refinement of
its generated encoders/decoders against the independent Lean wire spec. Then
replace the persistent local key with a memory-only credential agent and
harden crash/rollback and filesystem races.

### Secure v3 endpoint step: no disk-resident derived key

- Added a dedicated Unix credential agent (`rust/crates/transcrypt-v3/src/session.rs`).
  The key is sent once over a private pipe, kept in the agent, and never
  returned over Git-filter IPC or written to `.git`.
- Switched `clean`, `smudge`, pre-commit index validation, hydrate, and lock
  to the same authenticated in-process crypto service. Per-request public
  config binding prevents a stale session from silently accepting changed
  metadata. `lock` terminates the agent after a successful ciphertext flush.
- Corrected `hydrate` to restore from the staged index rather than `HEAD`.
  Added refusal of symlinked parents of protected worktree files, plus test
  cases for key absence, session lifetime and staged-index hydration.
- Verification gate on the user's Rust toolchain: `cargo test --workspace`
  followed by `cargo build --release -p transcrypt-v3`. No Rust compiler or
  Lean/Aeneas runner is present in the artifact environment; do not claim
  compilation until the user runs those commands.
- Open security limitations: same-UID code can use the socket, OS swap/core
  dumps are outside the guarantee, metadata/Git transitions are not atomic,
  and dirfd-based race-hardening plus independent crypto review remain.

### Correct encrypted-checkout hydration after live-agent integration

- The first live-agent integration test exposed a Git behavior: `git restore
  --worktree` calls `clean` while refreshing a ciphertext worktree in some
  configurations. The clean filter correctly rejects raw ciphertext; therefore
  hydration cannot delegate to `git restore` or relax filter strictness.
- Updated `hydrate` to preflight authenticated index objects and worktree
  contents, then write authenticated plaintext via private temporary files
  and atomic per-file rename. A second run accepts unchanged already-hydrated
  plaintext and can continue an interrupted multi-file operation. Git's cached
  worktree stat entries are refreshed using the normal clean filter only
  **after** plaintext is present, followed by a strict index identity check.
- Expanded the Git integration test to exercise multi-file preflight failure,
  idempotent hydration, and the staged-index-versus-HEAD divergence case.
- **Validation gate:** run `cargo test --workspace` and
  `cargo test -p transcrypt-v3 --test git_lifecycle` on a Rust-enabled machine.
  The artifact environment did not compile Rust. Filesystem operations still
  lack full crash transactions and dirfd-based protection against concurrent
  same-UID path replacement.
