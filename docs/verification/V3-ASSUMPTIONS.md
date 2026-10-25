# Transcrypt v3: assumption register

**Created 2026-10-25; reconciled after the security-hardening campaign of
2026-10-25.** Every guarantee about the Rust v3 implementation is
conditional on the assumptions below. Identifiers are stable: A1–A10 keep
their meaning, and A11–A14 were added when this campaign surfaced them.
Assumptions are listed from **least trusted** (our own newest code) to
**most trusted** (standard cryptographic hardness).

Status vocabulary (see [V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md)):
**PROVED** = Lean theorem about the Aeneas translation of production Rust;
**PROVED (model)** = Lean theorem about a model of adapter sequencing;
**TESTED** = real Rust/Git tests, fault injection or independent
implementations; **REVIEWED** = argued in a document; **ASSUMED** = stated
and bounded, not discharged; **ACCEPTED RISK** = a documented limitation.
TESTED is never PROVED, and a reviewed adapter call site is not a verified
one.

## Summary

| # | Short name | Status |
| --- | --- | --- |
| A1 | Protocol decision core is correct | PROVED |
| A2 | Wire codec matches the spec | PROVED |
| A3 | Charon/Aeneas/hax translation and Lean are sound | ASSUMED (pinned, reproduced) |
| A4 | Adapter invokes the core correctly and obeys it | Narrowed: structural (object-id snapshot, stamps, literal Git paths) + PROVED (model) + REVIEWED + TESTED |
| A5 | `Keyed` realizes the primitive contract | TESTED (differential vs OpenSSL, exhaustive tampering) |
| A6 | Credential agent relays core results faithfully | TESTED + REVIEWED; same-UID ACCEPTED RISK |
| A7 | Git semantics | TESTED on Git 2.43; ASSUMED otherwise |
| A8 | OS / filesystem behavior | Narrowed + TESTED (SIGKILL fault injection); same-UID races ACCEPTED RISK |
| A9 | RustCrypto implementations are correct | TESTED (differential); no external audit |
| A10 | AES-SIV, Argon2id, SHA-256 security | ASSUMED (standard) |
| A11 | A Git object id names exactly one content | ASSUMED (Git's hash) |
| A12 | File stamps change on modification; v3 processes honor the staging lock | TESTED |
| A13 | History is audited before it reaches others (deployment) | REVIEWED; depends on deployment |
| A14 | Keyless envelope checks only stop accidental plaintext | ACCEPTED RISK (by design) |

## Detailed register

### A1 — Protocol decision core

- **Claim:** `transcrypt-v3-core` decides correctly: path policy, config
  authentication, seal/open gates and their order, envelope and config
  binding, double-encryption refusal, size bounds, output zeroing,
  hydrate/lock actions, agent authorization, the Git `check-attr` verdict,
  index-record parsing, object-id syntax and keyless envelope checks.
- **Trust boundary:** our Rust, `no_std`, extracted by Charon/Aeneas.
- **Consequence if false:** any security property.
- **Evidence:** PROVED against the independent spec `V3Policy.lean`; see
  [Discharged by proof](#discharged-by-proof).
- **Residual:** only through A3 and the contract A5.
- **Next reduction:** none needed; keep every new decision in the core.
- **Status:** PROVED.

### A2 — Wire codec

- **Claim:** 55-byte config and 22-byte header encoders/decoders and the
  slice-length gates match the spec.
- **Evidence:** PROVED (all fields, every outcome, roundtrips).
- **Status:** PROVED.

### A3 — Translation and kernel soundness

- **Claim:** the Aeneas translation means what the Rust means; Lean's kernel
  is sound.
- **Trust boundary:** cargo-hax 0.4.2 (Charon + Aeneas), Lean 4, mathlib.
- **Consequence:** A1/A2 proofs could be about a different program.
- **Evidence:** pinned toolchain; CI re-extraction reproduces the tracked
  snapshot byte-for-byte; the same Rust functions are exercised by unit,
  integration and differential tests; axiom audit shows only `propext`,
  `Classical.choice`, `Quot.sound`.
- **Residual:** a translator bug that tests happen not to exercise.
- **Next reduction:** differential execution of the extracted definitions
  once they can be made computable.
- **Status:** ASSUMED.

### A4 — Adapter-to-core correspondence

- **Claim:** the effectful adapter (`main.rs`, `session.rs`, `lib.rs`,
  `fsat.rs`) passes the core the right bytes (exact Git path, on-disk config,
  staged record), acts only on `Ok` results, and acts on the *same* bytes it
  checked.
- **Trust boundary:** our unverified Rust.
- **Consequence:** a verified decision about one set of bytes is applied to
  another, releasing or staging plaintext.
- **Evidence:**
  - **Structural (this campaign).**
    - Every Git object is read through the object id in one parsed index or
      tree snapshot (`git cat-file blob <oid>`, ids checked by the proved
      `is_object_id`). Content addressing (A11) therefore guarantees that the
      bytes used are the bytes verified.
    - `:<path>` revision syntax is gone.
    - Every Git subprocess runs with literal pathspecs and without replace
      refs.
    - Worktree replacement requires the stamp from the check that justified
      it.
    - `hydrate`/`lock` re-index only the verified paths, through
      `update-index -z --stdin`, which takes no pathspecs and adds no files.
  - **PROVED (model).** Lifecycle sequencing: `hydratePlan_spec`,
    `lockEntry_spec`, `verifyPlan_spec`.
  - **REVIEWED.** [Call-site table](#adapter-call-site-table-a4).
  - **TESTED.** Real-Git lifecycle and adversarial suites, including
    pathspec-magic and revision-syntax filenames, and SIGKILL fault
    injection.
- **Residual:** the adapter Rust itself is not proved. The oid slice
  `entry[7..path_start-3]` is justified by the parser's spec, not proved in
  the adapter.
- **Next reduction:** move the oid offset into `IndexEntry` (a proved field).
  Then batch object reads through one `git cat-file --batch` with proved
  header parsing.
- **Status:** narrowed; PROVED (model) + REVIEWED + TESTED.

### A5 — `Keyed` realizes the primitive contract

- **Claim:** `Keyed` computes RFC 5297 AES-256-SIV with AD vector
  `[domain, config, path]` (three S2V components, not a concatenation),
  SHA-256 truncation, exact output lengths, and never reports false success.
  These are the clauses of Lean's `Realizes`.
- **Trust boundary:** `transcrypt-v3/src/lib.rs` plus A9.
- **Consequence:** the C-02 theorems would be about a different primitive.
- **Evidence:**
  - TESTED by `v3_differential.rs` against OpenSSL AES-SIV and reference
    Argon2id. It covers 22 lengths across every AES/CMAC block boundary
    (0–16385 bytes), random raw-byte paths, and three passphrase extremes.
    For each case it checks: byte equality; every bit flip of short records
    and of headers/tags; spread flips over bodies; truncation; extension;
    wrong and prefix paths; another repository; another key; and wrong
    output size.
  - The Python generator also asserts that concatenated AD gives a
    *different* SIV.
  - Contract clauses are tested directly in
    `keyed_satisfies_the_realizes_contract`.
- **Residual:** inputs outside the corpus; RustCrypto internals (A9).
- **Next reduction:** a coverage-guided fuzz target comparing against
  OpenSSL.
- **Status:** TESTED.

### A6 — Credential agent

- **Claim:** the agent holds the key only in memory, answers only framed
  requests for the authenticated config, and returns the core's results
  unchanged.
- **Trust boundary:** our `session.rs`; Unix sockets; process isolation.
- **Consequence:** key or plaintext exposure to another process; forged
  results.
- **Evidence:**
  - Key only via a startup pipe.
  - Authorization and framing PROVED.
  - The session directory and socket must be owned by this UID, with modes
    0700 and 0600.
  - Both client and agent refuse a peer with another UID (`SO_PEERCRED` /
    `getpeereid`).
  - 120 s read and write timeouts.
  - Non-dumpable, no core dumps, key page `mlock`ed.
  - TESTED by hostile-client, stale-socket and dumpability tests.
- **Residual:** any same-UID process can use or impersonate the agent while
  unlocked (ACCEPTED RISK; it needs a different privilege boundary).
  Plaintext buffers are not `mlock`ed. The agent never times out.
- **Next reduction:** an optional idle timeout; a separate UID or OS keyring
  if the threat model ever admits hostile same-UID code.
- **Status:** TESTED + REVIEWED; same-UID ACCEPTED RISK.

### A7 — Git semantics

- **Claim:**
  - `%f` passes exact path bytes.
  - `ls-files --stage -z`, `ls-tree --format`, `check-attr --cached -z` and
    `cat-file blob` behave as documented.
  - `filter.<d>.required` is enforced.
  - `update-index --stdin` takes literal paths and never adds files.
  - `GIT_LITERAL_PATHSPECS` and `GIT_NO_REPLACE_OBJECTS` are honored.
  - The pre-commit hook sees the index being committed (`GIT_INDEX_FILE`).
- **Consequence:** wrong bytes authenticated, or protected files not
  filtered.
- **Evidence:** TESTED with real Git 2.43 (raw and non-UTF-8 paths, glob and
  magic filenames, attribute precedence, index/HEAD divergence). `audit`
  requires Git ≥ 2.36.
- **Residual:**
  - Other Git versions.
  - Attributes that transform stored bytes (`text`, `eol`, `ident`,
    `working-tree-encoding`) corrupt records; this fails closed but blocks
    use.
- **Next reduction:** a CI matrix over Git versions; check those attributes
  in `check-attr` for a clearer error.
- **Status:** TESTED (one Git version), ASSUMED otherwise.

### A8 — OS and filesystem

- **Claim:** `renameat` is atomic within a filesystem, fsync is durable,
  permissions are enforced, `openat(O_NOFOLLOW)` resolution is sound, and
  core-dump/ptrace controls work.
- **Consequence:** plaintext left outside protected files, lost edits, or a
  readable key.
- **Evidence:**
  - Narrowed: fd-relative resolution; private 0700 staging; stamp check
    before every rename; exclusive staging lock.
  - TESTED by SIGKILL fault injection at 12 points through `lock`/`hydrate`
    on 22 files. Every protected file stays exactly ciphertext or plaintext,
    no file appears in the worktree, and every rerun converges.
  - Also TESTED: symlink/parent-swap races, crash leftovers and dumpability.
- **Residual:**
  - A same-UID writer can win the window between the final stamp check and
    `renameat`.
  - Hard links to a plaintext file survive `lock`.
  - Root; hibernation and swap of non-key buffers.
  - Files written by Git's checkout follow the umask.
  - All ACCEPTED RISK.
- **Next reduction:** warn on `nlink > 1` at lock; tighten modes of
  plaintext files `hydrate` keeps.
- **Status:** narrowed + TESTED; same-UID ACCEPTED RISK.

### A9 — RustCrypto implementations

- **Claim:** `aes-siv 0.8.0`, `aes 0.9.3`, `cmac 0.8.0`, `ctr 0.10.1`,
  `argon2 0.6.0`, `sha2 0.10.9` (pinned with `=`) and their locked
  transitive dependencies (`ctutils 0.4.5`, `cmov 0.5.4`) are correct and
  constant-time where required.
- **Consequence:** A5 fails; a timing leak of the SIV tag comparison.
- **Evidence:**
  - TESTED by differential tests against independent implementations
    (A5).
  - RustSec advisory database checked 2026-10-25. The locked `ctutils`
    0.4.5 and `cmov` 0.5.4 contain the fixes for RUSTSEC-2026-0385 and
    RUSTSEC-2026-0003 (non-constant-time masks/compares in the path of the
    SIV tag check).
  - CI now runs `cargo audit --deny warnings`.
  - Zeroization:
    - `zeroize` features on aes/cmac/ctr/aes-siv and on argon2.
    - Argon2id runs in caller-owned memory that is wiped. The library frees
      its own blocks unwiped, even with `zeroize`.
    - SIV runs in place in caller buffers.
- **Residual:** no independent audit of `aes-siv`; constant-time properties
  are not verified by us.
- **Next reduction:** external review (R-01).
- **Status:** TESTED; review outstanding.

### A10 — Cryptographic hardness

- **Claim:** AES-SIV is a secure deterministic AEAD; Argon2id
  (m = 64 MiB, t = 3, p = 1) resists offline guessing; SHA-256/128 is an
  adequate public discriminator.
- **Residual:** equality leakage per path (inherent to deterministic
  filters); offline guessing of weak passphrases (≥ 16 bytes enforced); Git
  history rollback (no freshness state).
- **Status:** ASSUMED (standard); limitations ACCEPTED.

### A11 — Git object identity (new)

- **Claim:** a Git object id names exactly one content, so bytes read twice
  by id are the bytes that were verified.
- **Trust boundary:** Git's object store; SHA-1 with collision detection
  (default) or SHA-256 repositories.
- **Consequence:** a crafted collision could substitute content between
  verification and use. This needs a chosen-prefix SHA-1 collision that
  defeats Git's collision detection, plus same-UID write access to the
  object store.
- **Evidence:** standard Git integrity assumption; replace refs disabled.
- **Status:** ASSUMED.

### A12 — Stamps and the staging lock (new)

- **Claim:** any write, truncation, replacement or chmod of a file changes
  its (device, inode, size, mtime, ctime) stamp. All v3 processes take the
  exclusive `flock` on `.git/transcrypt-v3-staging` before mutating the
  worktree.
- **Consequence:** a concurrent edit between check and replace is lost.
- **Evidence:** TESTED (`replacement_refuses_a_file_changed_since_it_was_checked`,
  concurrent-entry refusal); ctime cannot be set by unprivileged
  `utimensat`.
- **Residual:** filesystems with coarse timestamps *and* writes that
  preserve size and inode within one tick; non-v3 writers do not take the
  lock.
- **Status:** TESTED.

### A13 — History is audited before others rely on it (new, deployment)

- **Claim:** plaintext committed where no v3 filter ran never reaches a
  shared remote. Examples: a clone that never ran `unlock`, merges and
  rebases that skip `pre-commit`, `--no-verify`.
- **Trust boundary:** the installed `pre-push` hook, or `transcrypt-v3 audit`
  in CI or a server-side hook.
- **Consequence:** plaintext published.
- **Evidence:** TESTED (pre-push refuses a `--no-verify` plaintext commit; a
  keyless `audit` in a never-unlocked clone refuses its plaintext commit).
- **Residual:** `git push --no-verify`; repositories that deploy neither the
  hook nor a server-side audit; a fresh clone has no hooks at all. Git
  offers no repository-controlled enforcement.
- **Next reduction:** document and ship a ready-made CI/pre-receive
  snippet.
- **Status:** REVIEWED + TESTED; enforcement depends on deployment.

### A14 — Keyless checks are envelope checks (new, by design)

- **Claim:** while locked, and in a keyless `audit`, a protected blob is
  accepted if it has the v3 envelope (header, config id, size). Locked
  filters pass such records through unchanged.
- **Consequence:** a record that only *looks* authentic is committed or
  checked out; this is detected (fail closed) at the next unlocked
  `verify-index`, `hydrate` or keyed `audit`. Releasing plaintext is
  unaffected: it always requires full authentication (A1).
- **Evidence:** PROVED that the check accepts every genuine record
  (`opensTo_envelopeOk`) and is exactly the spec predicate
  (`record_envelope_ok_spec`). It rejects every accidental plaintext, since
  that would need the 6-byte magic plus 16 bytes of the config's SHA-256.
- **Status:** ACCEPTED RISK (forgery detection deferred to unlocked checks).

## Ranked unresolved risks

Ranked by exploitability × impact under the threat model (a non-root
attacker controlling the remote and history, not the user's account), then
by cost.

1. **Plaintext from checkouts without v3 filters (A13).** Most likely real
   leak: a collaborator commits a `*.secret` in a clone that never ran
   `unlock`. *Strongest next action:* make server-side `audit` part of the
   documented setup (CI snippet), and consider refusing `status`/`audit`
   success when hooks are bypassed.
2. **No external review (R-01, A9).** *Action:* independent cryptographic
   and adapter review using [the review package](V3-SECURITY-REVIEW.md#review-package).
3. **Same-UID processes (A6, A8).** Any program running as the user can use
   the unlocked agent or race file contents. Requires a privilege boundary
   to fix. *Action:* document; optional idle timeout.
4. **Plaintext permissions from Git checkout (A8).** Smudge output follows
   the umask. *Action:* hydrate could tighten kept plaintext files; the
   guide requires `umask 077`.
5. **Unverified adapter remainder (A4).** *Action:* move the oid offset into
   the proved parser and batch object reads.
6. **Git-version drift (A7).** *Action:* CI matrix over Git versions.
7. **Rollback and equality leakage (A10).** Protocol limits, accepted.

## Discharged by proof

All theorems below are about the Aeneas translation of the production core
and compile without `sorry`; `check-v3-axioms.sh` shows only Lean's standard
axioms. Statement details: [PROOF-STATUS](../../proofs/aeneas/v3/PROOF-STATUS.md).

| Previously trusted | Theorem(s) |
| --- | --- |
| Encoders write the spec layout | `encode_config_bytes`, `encode_config_refines`, `encode_file_header_bytes`, `encode_file_header_refines` |
| Decoders and public parsers implement the spec grammar | `decode_*_exact_spec`, `parse_config_spec`, `parse_file_header_spec`, roundtrips |
| Path canonicalization policy | `is_canonical_protected_path_spec` |
| Config authentication | `authenticate_config_spec`, `initialize_config_spec` |
| Clean never emits anything but a correct record, never double-encrypts | `seal_record_spec` |
| Smudge/verify release only authentic plaintext for this config and path | `open_record_spec`, `open_record_complete`, `opensTo_unique` |
| Agent authorization and framing | `authorize_agent_request_spec`, `decode_frame_header_encode` |
| Effective filter attribute check | `check_attr_response_ok_spec`, `check_attr_paths` |
| Index record parsing | `parse_index_entry_spec` |
| Object ids passed to Git are plain hex names | `is_object_id_spec`, `objectId_plain` |
| Keyless envelope check | `record_envelope_ok_spec`, `opensTo_envelopeOk` |
| Hydrate/lock never lose data; verify-index soundness | `hydrate_action_spec`, `lock_action_spec`, `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` |

## Adapter call-site table (A4)

Each effect in `rust/crates/transcrypt-v3/src/{main,session,lib}.rs` and the
verified decision that gates it:

| Adapter action | Gate (verified core function) | Inputs passed | Acts only on |
| --- | --- | --- | --- |
| `clean` filter output (unlocked) | agent `Encrypt` → `clean_file`: `open_record` (authentic record ⇒ returned unchanged) else `seal_record` | config bytes from `.transcrypt/config`; Git `%f` bytes; stdin | `Ok` (else Git aborts) |
| `smudge` filter output (unlocked) | agent `Decrypt` → `open_record` | same config; `%f`; blob from stdin | `Ok` |
| `clean`/`smudge` while locked | `record_envelope_ok` against `config_id(config)` | stdin | `true` ⇒ input unchanged; else refuse |
| Agent framing | `encode_frame_header` / `decode_frame_header`, `encode_be_u32` / `decode_be_u32` | opcode, config, lengths | proved roundtrip |
| Agent dispatch | `authorize_agent_request` before the body is read; peer UID check | opcode, supplied config, startup config, path, length | `Ok(op)` from a same-UID peer |
| Agent startup | `authenticate_config` | config bytes, piped key | `Ok` |
| `unlock` / `init` | `authenticate_config` / `initialize_config` | config bytes / fresh salt | `Ok`, before any persistent effect |
| Index and tree listings | `parse_index_entry`, then `is_object_id` on `entry[7..path_start-3]` | each NUL-delimited `ls-files --stage -z` / `ls-tree --format` record | `Ok` and `true` (else refuse) |
| Object reads | `is_object_id` | oid from the parsed snapshot | `true`; read ≤ 16 MiB via `cat-file blob` |
| `verify-index` | `check_attr_response_ok`, then agent `Decrypt` per entry (or `record_envelope_ok` while locked) | exact `check-attr` request; snapshot paths; blobs by oid | `true` / `Ok` for every entry |
| `hydrate` publish | agent `Decrypt`, then `hydrate_action`, all entries before any write; stamp equality | blob by snapshot oid; worktree bytes and stamp via held dirfd | `Ok(Publish)` for all; `Keep` untouched |
| `lock` flush | agent `Encrypt` (reseal), then `lock_action`; stamp equality | worktree bytes and stamp, blob by oid, reseal output | `Ok(Flush)`; `Keep` untouched |
| Re-index after hydrate/lock | none (bookkeeping); listing compared with the verified snapshot afterwards | verified protected paths, raw, via `update-index -z --stdin` | listing unchanged |
| `audit` / `pre-push` | `parse_index_entry`, `is_object_id`, `parse_config`, `record_envelope_ok`, agent `Decrypt` when it serves that config | `ls-tree` per commit; blobs by oid | every protected entry `true`/`Ok` |
| Protected file selection | `is_protected_path` | index/tree path bytes | — |

The Lean lifecycle models (`Lifecycle.lean`) reproduce the hydrate, lock and
verify loops in this order. Review rule: a new effect in the adapter must
appear in this table with its gate, or it is a regression.
