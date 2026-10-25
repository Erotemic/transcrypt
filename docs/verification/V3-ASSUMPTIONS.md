# Transcrypt v3: assumption register

**Created 2026-10-25; reconciled after the security-hardening campaign of
2026-10-25.** Every guarantee about the Rust v3 implementation is
conditional on the assumptions below. Identifiers are stable: A1–A10 keep
their meaning, and A11–A14 were added when this campaign surfaced them.
A16–A18 were opened by the [product charter](V3-PRODUCT-CHARTER.md) and
the independent review, and are now implemented and tested; A19 was added
with attribute-based selection. Older security-hardening priorities are
superseded by the charter where they conflict (for example, private worktree
permissions are now an optional mode); the source-derived proof status and
existing assumption meanings are not.

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
| A6 | Private-mode credential agent relays core results faithfully | TESTED + REVIEWED; same-UID ACCEPTED RISK (optional mode) |
| A7 | Git semantics | TESTED on Git 2.43; ASSUMED otherwise |
| A8 | OS / filesystem behavior | Narrowed + TESTED (SIGKILL fault injection); same-UID races ACCEPTED RISK |
| A9 | RustCrypto implementations are correct | TESTED (differential); no external audit |
| A10 | AES-SIV, Argon2id, SHA-256 security | ASSUMED (standard) |
| A11 | A Git object id names exactly one content | ASSUMED (Git's hash) |
| A12 | File stamps change on modification; v3 processes honor the staging lock | TESTED |
| A13 | History is audited before it reaches others (deployment) | REVIEWED; depends on deployment |
| A14 | Keyless envelope checks only stop accidental plaintext | ACCEPTED RISK (by design) |
| A15 | Git creates worktree files with the umask its filters inherit | TESTED (Git 2.43; CI 2.34, Apple Git); private mode only |
| A16 | Git-attribute selection: every decision uses Git's own answer for the exact path | Parsing PROVED; selection by Git ASSUMED (A19); TESTED end to end |
| A17 | The stored key is local-only, used only for the config it authenticates, and mode-independent | TESTED + REVIEWED; local-account exposure ACCEPTED RISK (by charter) |
| A18 | Path-bound renames are re-encrypted for the new path, never laundered | Decision PROVED (`seal_action`); TESTED (real Git) + REVIEWED |
| A19 | Git evaluates `filter` the same way for its filters, `check-attr --cached` and a commit's attribute files | TESTED (Git 2.43; CI 2.34); local override files ACCEPTED RISK |

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

- **Claim:** the effectful adapter (`main.rs`, `git.rs`, `worktree.rs`,
  `setup.rs`, `audit.rs`, `session.rs`, `lib.rs`, `fsat.rs`) passes the core the right bytes (exact Git path, on-disk config,
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
    `lockEntry_spec`, `verifyPlan_spec`. Filter behavior: `cleanModel_spec`,
    `cleanModel_genuine`, `cleanModel_idempotent` (unlocked clean stores
    only genuine records) and `lockedFilterModel_spec` (locked filters emit
    only unchanged envelopes).
  - **REVIEWED.** [Call-site table](#adapter-call-site-table-a4).
  - **TESTED.** Real-Git lifecycle and adversarial suites, including
    pathspec-magic and revision-syntax filenames, and SIGKILL fault
    injection.
- **Residual:** the adapter Rust itself is not proved. The oid slice
  `entry[7..path_start-3]` is proved to extract the object id of every
  accepted record (`indexRecord_oid`), but the Rust slice expression itself
  is reviewed, not extracted.
- **Next reduction:** object reads now go through one `git cat-file --batch`
  per process with an exact, re-serialized header check; moving that check
  into the proved core is the remaining step.
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

### A6 — Private-mode credential agent

- **Claim:** in the optional private mode (`unlock --private`), the agent
  holds the key only in memory, answers only framed requests for the
  authenticated config, and returns the core's results unchanged. The
  default mode has no agent (A17).
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
  - TESTED by hostile-client, fuzzed-frame, stale-socket and dumpability
    tests (all run in private mode).
  - Both modes produce byte-identical records
    (`stored_and_private_modes_encrypt_identically`).
- **Residual:** any same-UID process can use or impersonate the agent while
  unlocked (ACCEPTED RISK; it needs a different privilege boundary).
  Plaintext buffers are not `mlock`ed. The agent never times out.
- **Next reduction:** an optional idle timeout; a separate UID or OS keyring
  if the threat model ever admits hostile same-UID code.
- **Status:** TESTED + REVIEWED; same-UID ACCEPTED RISK.

### A7 — Git semantics

- **Claim:**
  - `%f` passes exact path bytes.
  - `ls-files --stage -z`, `ls-tree -r -z`, `check-attr --cached -z` and
    `cat-file blob` behave as documented.
  - `filter.<d>.required` is enforced.
  - `update-index --stdin` takes literal paths and never adds files.
  - The long-running filter protocol (version 2) frames each request as
    documented (`command=`, `pathname=` with the exact path bytes, content
    up to a flush), and Git fails the command when a required filter
    returns `status=error` or exits.
  - `GIT_LITERAL_PATHSPECS` and `GIT_NO_REPLACE_OBJECTS` are honored.
  - The pre-commit hook sees the index being committed (`GIT_INDEX_FILE`).
  - `rev-parse --path-format=absolute --git-dir --git-common-dir` and
    `worktree list --porcelain` identify a worktree's own and shared Git
    directories and the repository's other worktrees.
- **Consequence:** wrong bytes authenticated, or protected files not
  filtered.
- **Evidence:** TESTED with real Git 2.43 (raw and non-UTF-8 paths, glob and
  magic filenames, attribute precedence, index/HEAD divergence).
- **Residual:**
  - Other Git versions.
  - Attributes that transform stored bytes (`text`, `eol`, `ident`,
    `working-tree-encoding`) corrupt records; this fails closed but blocks
    use.
- **Next reduction:** CI now runs the suite on Git 2.34 (Ubuntu 22.04),
  2.43 (Ubuntu 24.04) and Apple Git (macOS); check transforming attributes
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
  - Files the user creates follow their umask until `git add` (the clean
    filter) or `hydrate` makes them private (Git itself no longer writes
    readable plaintext: A15).
  - All ACCEPTED RISK.
- **Next reduction:** done: `lock` warns on `nlink > 1`; `hydrate` makes
  kept plaintext private. Remaining: none cheap.
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
  offers no repository-controlled enforcement. Plaintext copies of secrets
  under other names: the well-known editor and merge copy names are
  excluded locally and refused by `audit`, but any other name is not
  recognized.
- **Next reduction:** done in these campaigns: a CI snippet (user guide); a
  server hook `contrib/v3/pre-receive` with a work budget (TESTED against a
  bare repository with a client that skipped its own hook); `doctor` for
  local gaps; and `contrib/v3/check-remote-enforcement` to confirm that a
  remote rejects plaintext. What remains is deploying them, which is the
  repository owner's decision.
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

### A15 — Git applies its filters' umask to new worktree files (private mode)

- **Claim:** the umask a smudge filter inherits is the umask Git applies
  when it creates the worktree file (`0666 & ~umask`, or `0777` for
  executables). So a filter that sees a private umask knows Git will write a
  private file. Only the private mode relies on this; the default mode lets
  plaintext follow the user's umask, as any file does.
- **Trust boundary:** Git's checkout code (`entry.c`) and POSIX `open`.
- **Consequence if false:** in private mode, plaintext written by Git could
  be readable by other local users (H-16 would reopen there).
- **Evidence:** TESTED against real Git:
  - `git_never_writes_plaintext_readable_by_others` (private mode) checks
    every protected file after checkout, merge, rebase, stash, stash pop and
    restore, under `umask 022` and `077`;
  - the assumption is consistent with Git's documented checkout behavior.
- **Residual:**
  - a Git that writes worktree files with a mode independent of the umask
    (no known version);
  - plaintext a user creates themselves (A8).
- **Next reduction:** none needed unless a Git version behaves differently.
- **Status:** TESTED; optional-mode guarantee.

### A16 — Selection by Git attributes

- **Claim:** a path is protected exactly when Git's effective `filter`
  attribute for it is `transcrypt-v3` (reserved metadata excepted), and
  every v3 decision (clean, smudge, verify, hydrate, lock, status, audit)
  uses that answer for the exact path bytes. v3 never matches patterns
  itself.
- **Trust boundary:** Git's attribute evaluation (A19); our request
  construction (`protected_flags`: raw paths, `-z --stdin`); the verified
  parser `parse_attr_record`.
- **Consequence if false:** a protected file stored or checked as
  unprotected (plaintext published), or a public file treated as protected.
- **Evidence:**
  - `parse_attr_record` PROVED to accept exactly
    `path NUL filter NUL value NUL` for the requested path, and to report
    `protected` iff the value is `transcrypt-v3`; the adapter requires every
    record in order and the response consumed exactly.
  - The path policy (`is_canonical_protected_path`) is suffix-free and PROVED:
    any canonical path except `.transcrypt/…`, `.gitattributes` and
    `.gitmodules`.
  - TESTED: `.env`, a file in a directory, `private/**`, `*.key`, a quoted
    name with spaces, a name with a quote, newline and a non-UTF-8 byte, an
    executable, a nested `.gitattributes`, an exclusion, clone, lock and
    unlock (`arbitrary_patterns_protect_exactly_the_selected_files`);
    policy changes, reserved patterns and `unprotect`
    (`protect_and_unprotect_change_the_policy_explicitly`).
  - The audit evaluates each commit with that commit's own attribute files
    (a temporary index), so history is judged by the policy it was
    committed under.
- **Residual:** the staged policy (`check-attr --cached`) decides
  verification, while `git add` applies the worktree policy; an unstaged
  `.gitattributes` edit can differ until it is staged (`protect` stages it).
  Local override files (A19).
- **Next reduction:** the adapter's record loop is now a proved model
  (`attrFlagsModel_sound`/`_complete`); what remains is that
  `protected_flags` follows it (A4).
- **Status:** parsing and path policy PROVED; Git's evaluation ASSUMED (A19);
  TESTED end to end.

### A17 — Stored key (the default unlock)

- **Claim:** `unlock` stores the Argon2id-derived key, never the
  passphrase, only in `$GIT_COMMON_DIR/transcrypt-v3/key` (a regular 64-byte
  file, mode 0600, in a 0700 directory owned by the user, outside `git
  config`). Every use authenticates the current `.transcrypt/config` with
  it first; a key that does not authenticate (a pulled rekey) is treated as
  locked. The ciphertext does not depend on the mode.
- **Trust boundary:** our `credential.rs`; the local file system; Git's
  common directory for worktrees.
- **Consequence if false:** a key in public or shared state; a key used for
  another config (records under the wrong config, refused later by
  verification); different ciphertext per mode.
- **Evidence:**
  - Written via an exclusive 0600 temporary, `fsync` and `renameat` in the
    held, checked directory; read with `O_NOFOLLOW`, exact size required.
  - `assert_unlocked` (git_lifecycle): exactly one private 64-byte key file,
    no agent, no passphrase in `.git/config` or the key file.
  - Stale key after a pulled rekey decrypts and encrypts nothing until
    `unlock` (`pulled_rekey_makes_the_stored_key_stale_until_unlock`).
  - Mode independence (`stored_and_private_modes_encrypt_identically`).
  - `lock` deletes it; `uninstall` deletes it.
- **Residual (ACCEPTED, by the charter):** anything that can read the
  user's files (other same-UID programs, backups, copies of `.git`) can use
  the key, as it can read the unlocked plaintext. Deleting the file is not a
  secure erasure.
- **Next reduction:** none planned for the default; private mode is the
  stricter alternative.
- **Status:** TESTED + REVIEWED.

### A18 — Authenticated path rebinding on rename

- **Claim:** a `git mv` of a protected file, made locally, is re-encrypted
  for its new path before it is committed; content that arrived in a commit
  (pull, merge, rebase) is never re-encrypted for another path, so a hostile
  move is refused, not laundered; while locked, a moved record is refused.
- **Trust boundary:** Git `mv` staging behavior; the pre-commit hook
  (`seal_staged`), which re-encrypts only through `open_record` at the old
  path and `seal_record` at the new one; keyless checks in `check_index` and
  `audit`.
- **Consequence if false:** an undecryptable record at the new path (data
  needs recovery from the old path), or a hostile move accepted as genuine.
- **Evidence:**
  - Rebinding requires: no merge, cherry-pick, revert or rebase in progress;
    the staged blob differs from `HEAD`'s at that path; the source path is
    in `HEAD`, no longer in the index, and the record opens there.
  - TESTED: files, directories, unprotected→protected
    (`renames_are_re_encrypted_for_their_new_path`); locked move refused at
    commit and unbound move refused by keyless audit
    (`locked_renames_and_unbound_moves_are_refused`); a committed hostile
    move refused by the hook (`git_lifecycle`).
  - Smudge of a moved record fails with instructions (`git add` re-cleans it).
- **Residual:**
  - `git commit -- <paths>` after `git mv` uses a temporary index, so the
    main index keeps the old record until the next `git add`.
  - A copy (not a move) of a record is detected keylessly only in the
    index, not in history.
  - A user who deliberately stages a hostile commit's tree over their own
    `HEAD` (`git restore --staged --source=…`) presents its moves as local
    ones. The hook then re-encrypts them, naming the source path. This is
    equivalent to running the `git mv` themselves.
  - Git's content-based rename detection cannot pair path-bound records, so
    a rename on one branch and an edit on another merge as modify/delete
    (recoverable in plaintext; tested).
- **Proof:** the decision itself is the verified `seal_action`
  (`seal_action_spec`, `sealSpec_repairs_only_local`: only a local change
  that does not already open is ever repaired). The adapter computes its
  inputs: `local` from `HEAD` and the sequencing state, and `moved` from
  `open_record` at a `HEAD` path that has left the index (A4).
- **Status:** decision PROVED; inputs TESTED + REVIEWED.

### A19 — Git's attribute evaluation (new)

- **Claim:** Git computes the effective `filter` attribute the same way for
  the filters it runs, for `git check-attr --cached` against the index, and
  for `check-attr --cached` against a temporary index holding a commit's
  `.gitattributes` blobs: patterns, nesting, precedence, macros,
  `.git/info/attributes` and `core.attributesFile`.
- **Trust boundary:** Git (`attr.c`).
- **Consequence if false:** selection disagreements between staging,
  verification and audit (A16).
- **Evidence:** TESTED on Git 2.43 (CI 2.34) through every selection test;
  the temporary-index technique works in bare repositories (server hook
  tests).
- **Residual (ACCEPTED):** local override files apply only locally: a
  `filter` rule in `.git/info/attributes` or the global attributes file can
  unprotect a file in this checkout, so local checks pass while a server
  audit (without those files) refuses the plaintext. `doctor` fails on such
  files and the pre-commit hook warns.
- **Status:** TESTED; overrides ACCEPTED RISK (an informed user's choice).

## Ranked unresolved risks and *product* opportunities

Ranked by violation of [the declared product promise](V3-PRODUCT-CHARTER.md),
realistic impact and effort.

1. **External crypto/adapter review** (A5/A9/R-01): required for credible
   release claims. Differential vectors reduce, but do not discharge, the
   trusted-library boundary.
2. **Adapter correctness** (A4/A7/A8/A16): the new selection, rebind and
   credential paths are tested and reviewed but not proved; the next proof
   targets are the attribute-record loop and the rebind decision.
3. **Deployment of history audits** (A13/A14): a clone that never unlocked
   commits plaintext; only a server or CI audit stops it reaching others.
4. **Local overrides and unconfigured clones** (A19): informed-user choices;
   reported by `doctor`, not prevented.
5. **Optional workstation privacy** (A6/A8/A15/A17): the stored key and the
   plaintext are readable by anything running as the user; private mode
   narrows this to the agent's lifetime.
6. **Inherent wire limits** (A10): offline guessing for weak passwords,
    deterministic equality, object metadata and historical rollback.

Closed by this campaign: F-02 (rekey symlink write), F-03 (`git mv`), F-04
(ignored chmod), F-01 (Bash v2 prefix bypass), arbitrary selection (A16),
persistent unlock (A17) and the v2 migration path.

## Discharged by proof

All theorems below are about the Aeneas translation of the production core
and compile without `sorry`; `check-v3-axioms.sh` shows only Lean's standard
axioms. Statement details: [PROOF-STATUS](../../proofs/aeneas/v3/PROOF-STATUS.md).

| Previously trusted | Theorem(s) |
| --- | --- |
| Encoders write the spec layout | `encode_config_bytes`, `encode_config_refines`, `encode_file_header_bytes`, `encode_file_header_refines` |
| Decoders and public parsers implement the spec grammar | `decode_*_exact_spec`, `parse_config_spec`, `parse_file_header_spec`, roundtrips |
| Path policy: canonical, any name except reserved metadata | `is_canonical_protected_path_spec`, `is_reserved_path_spec` |
| Config authentication | `authenticate_config_spec`, `initialize_config_spec` |
| Clean never emits anything but a correct record, never double-encrypts | `seal_record_spec` |
| Smudge/verify release only authentic plaintext for this config and path | `open_record_spec`, `open_record_complete`, `opensTo_unique` |
| Agent authorization and framing | `authorize_agent_request_spec`, `decode_frame_header_encode` |
| Parsing Git's attribute answers (what is protected) | `parse_attr_record_spec` (both directions), `attrResponse_recordAt`, `attrFlagsModel_sound`, `attrFlagsModel_complete` |
| Smudge keeps only genuine envelopes; opens only its own config | `smudge_action_spec`, `smudgeSpec_keep_envelope`, `smudgeModel_spec` |
| The pre-commit hook repairs only local changes | `seal_action_spec`, `sealSpec_repairs_only_local` |
| Index record parsing | `parse_index_entry_spec` |
| Git filter-protocol packet lengths | `decode_pkt_len_spec` |
| Object ids passed to Git are plain hex names, taken from the right bytes | `is_object_id_spec`, `objectId_plain`, `indexRecord_oid` |
| Keyless envelope check | `record_envelope_ok_spec`, `opensTo_envelopeOk` |
| Clean and locked-filter behavior (models of adapter compositions) | `cleanModel_spec`, `cleanModel_genuine`, `cleanModel_idempotent`, `lockedFilterModel_spec` |
| Hydrate/lock never lose data; verify-index soundness | `hydrate_action_spec`, `lock_action_spec`, `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` |

## Adapter call-site table (A4)

Each effect in `rust/crates/transcrypt-v3/src/{main,git,worktree,setup,audit,session,fsat,lib}.rs` and the
verified decision that gates it:

| Adapter action | Gate (verified core function) | Inputs passed | Acts only on |
| --- | --- | --- | --- |
| `clean` filter output (unlocked) | `Key::clean` → `clean_file` (stored key) or agent `Encrypt` (private): `open_record` (authentic record ⇒ returned unchanged) else `seal_record` | config bytes from `.transcrypt/config`; Git `%f` bytes; stdin | `Ok` (else Git aborts) |
| `smudge` filter output | `smudge_action` (no envelope ⇒ refuse; other config or locked ⇒ keep the record; own config ⇒ open), then `open_record`; private mode: `umask_is_private` chooses plaintext or the authenticated record | same config; `%f`; blob from stdin | `Ok` |
| `clean` while locked | `record_envelope_ok` against `config_id(config)` | stdin | `true` ⇒ input unchanged; else refuse |
| Key loading | `authenticate_config` with the stored key (else locked), or agent `Ping` | stored 64-byte key; current config | `Ok` |
| Protected-file selection | `parse_attr_record` per path, in order, response consumed exactly; `is_reserved_path` | raw paths sent to `check-attr -z --stdin filter` (`--cached`, worktree, or a commit's temporary index) | `protected = true` |
| Pre-commit re-encryption (`seal_staged`) | `seal_action` on (`open_record` at its path, local change, `parse_file_header`, `open_record` at the `HEAD` source path of a local move), then `clean_file`/`seal_record` at the new path | staged blobs by oid; `HEAD` listing; sequencing state | `Seal` or `Rebind` only |
| Agent framing | `encode_frame_header` / `decode_frame_header`, `encode_be_u32` / `decode_be_u32` | opcode, config, lengths | proved roundtrip |
| Git filter-process framing | `decode_pkt_len` for every packet; then the same conversion as the per-file filters | 4-byte pkt-line headers from Git; `command=`/`pathname=` values | `Ok` (else the process ends and Git fails) |
| Agent dispatch | `authorize_agent_request` before the body is read; peer UID check | opcode, supplied config, startup config, path, length | `Ok(op)` from a same-UID peer |
| Agent startup | `authenticate_config` | config bytes, piped key | `Ok` |
| `unlock` / `init` | `authenticate_config` / `initialize_config` | config bytes / fresh salt | `Ok`, before any persistent effect |
| Index and tree listings | `parse_index_entry`, then `is_object_id` on `entry[7..path_start-3]` | each NUL-delimited `ls-files --stage -z` record, or `ls-tree -r -z` record rewritten to that shape (path copied verbatim) | `Ok` and `true` (else refuse) |
| Object reads | `is_object_id` | oid from the parsed snapshot | `true`; one `cat-file --batch` per process; reply header must re-serialize exactly as `<oid> blob <size>`, size ≤ 16 MiB, trailing LF checked |
| `verify-index` | selection (above), then `open_record` per entry (or, while locked, `record_envelope_ok` and no other index/`HEAD` path with the same blob) | snapshot paths; blobs by oid | `true` / `Ok` for every entry |
| `hydrate` publish | agent `Decrypt`, then `hydrate_action`, all entries before any write; stamp equality | blob by snapshot oid; worktree bytes and stamp via held dirfd | `Ok(Publish)` for all; `Keep` untouched |
| `lock` flush | agent `Encrypt` (reseal), then `lock_action`; stamp equality | worktree bytes and stamp, blob by oid, reseal output | `Ok(Flush)`; `Keep` untouched |
| Re-index after hydrate/lock | none (bookkeeping); listing compared with the verified snapshot afterwards | verified protected paths, raw, via `update-index -z --stdin` | listing unchanged |
| `audit` / `pre-push` | `parse_index_entry`, `is_object_id`, `parse_config`, selection with the commit's attribute files, `record_envelope_ok`, no blob moved from a deleted path, `open_record` when the key authenticates that config | `ls-tree`/`diff-tree` per commit; blobs by oid | every protected entry `true`/`Ok` |
| `rekey` staging | `open_record` of each staged record, equality with the worktree, then `seal_record` under the new config (`encrypt_file`); `initialize_config` for the new config; config written by `write_repository_file` (dirfd, no symlinks) | staged blobs by oid, worktree bytes, fresh salt | all `Ok`, before any index or credential change |
| `protect` / `unprotect` / `init` / `migrate` | selection before and after the `.gitattributes` edit (written by `write_repository_file`); `seal_staged` with the newly selected paths; `open_record` before staging plaintext on `unprotect`; reserved metadata refused | attribute files; staged blobs | all `Ok`, or the edit is reverted |
| `uninstall` | `lock` (above), then `record_envelope_ok` for every protected worktree file | worktree bytes | all `true` before removing filters |
| `doctor` | none (read-only checks of Git config, attributes, hooks, `check_index`) | — | reports only |
| Merge driver | agent `Decrypt` (`open_record`) of ours and theirs at `%P` (base: empty if it does not open), `git merge-file`, agent `Encrypt` (`clean_file`) of the result | Git's `%O %A %B` files, `%P` path | both `Ok` (else `ours` is left unchanged and Git records a conflict) |
| Diff driver | `record_envelope_ok`, then agent `Decrypt` (`open_record`) of each record side at its own path | Git's external diff arguments | `Ok` (else Git stops the diff) |
| `hydrate` during a merge | unmerged paths: `record_envelope_ok`, agent `Decrypt`, `hydrate_action`; effective filter checked for every protected path | worktree bytes | `Ok(Publish)` |

The Lean lifecycle models (`Lifecycle.lean`) reproduce the hydrate, lock and
verify loops in this order. Review rule: a new effect in the adapter must
appear in this table with its gate, or it is a regression.
