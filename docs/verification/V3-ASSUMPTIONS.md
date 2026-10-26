# Transcrypt v3: assumption register

**Created 2026-10-25; reconciled after the security-hardening campaign of
2026-10-25.** Every guarantee about the Rust v3 implementation is
conditional on the assumptions below. Identifiers are stable: A1–A10 keep
their meaning, and A11–A14 were added when this campaign surfaced them.
A16–A18 were opened by the [product charter](V3-PRODUCT-CHARTER.md) and
the independent review, and are now implemented and tested; A19 was added
with attribute-based selection. A20–A23 name the Git contracts of the
[end-to-end security argument](V3-SECURITY-ARGUMENT.md), which now that the
hook's inputs are computed by the verified core are the remaining
assumptions of the pre-commit path. Older security-hardening priorities are
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
| A4 | Adapter invokes the core correctly and obeys it | Narrowed: structural (object-id snapshot, stamps, literal Git paths) + PROVED (model, incl. the end-to-end hook theorems) + REVIEWED + TESTED; the hook's inputs are now verified functions |
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
| A16 | Git-attribute selection: every decision uses Git's own answer for the exact path | Parsing PROVED (against the listing's own paths); selection by Git ASSUMED (A19); TESTED end to end |
| A17 | The stored key is local-only, used only for the config it authenticates, and mode-independent | Decision PROVED (`stored_key_state`, `stored_key_authenticates_current_config`); file I/O TESTED + REVIEWED; local-account exposure ACCEPTED RISK (by charter) |
| A18 | Path-bound renames are re-encrypted for the new path, never laundered | Decision and inputs PROVED (`seal_action`, `held_entries`, `is_local_change`, `next_move_source`, `hook_repairs_only_local_changes`); TESTED (real Git) + REVIEWED |
| A19 | Git evaluates `filter` the same way for its filters, `check-attr --cached` and a commit's attribute files | TESTED (Git 2.43; CI 2.34); local override files ACCEPTED RISK |
| A20 | Git prints its index and tree listings exactly (`ls-files --stage -z`; `ls-tree -r -z`, rewritten record by record) | TESTED; parsing PROVED (`parse_listing_spec`) |
| A21 | `cat-file --batch` answers the requested object, and the adapter reads exactly the announced content | Header and read decision PROVED (`parse_batch_header_spec`, `blob_read_spec`); content read TESTED |
| A22 | Git commits the index the pre-commit hook checked last | TESTED; ASSUMED (Git's commit flow) |
| A23 | The sequencing state names the commits being brought in (`MERGE_HEAD`, `CHERRY_PICK_HEAD`, `REVERT_HEAD`, `REBASE_HEAD`, rebase directories) | TESTED (merge, cherry-pick, rebase suites) |

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

- **Claim:** the effectful adapter (every module of
  `rust/crates/transcrypt-v3/src/` other than the core) passes the core the right bytes (exact Git path, on-disk config,
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
  - **PROVED (source-derived inputs, 2026-10-26).** The pre-commit hook and
    `verify-index` compute every input of their decisions with verified
    functions over the exact Git listings: `parse_listing`,
    `listing_fields`, `parse_listing_attrs`, `first_unselectable`,
    `held_entries`, `is_local_change`, `next_move_source`, `blob_elsewhere`;
    object replies are framed by `parse_batch_header` and `blob_read`; the
    stored key by `stored_key_state`. The end-to-end theorems
    (`hook_accepts_only_authenticated_ciphertext`,
    `hook_repairs_only_local_changes`,
    `stored_key_authenticates_current_config`) take the adapter's observed
    results of these calls as hypotheses (`HookRun`), so what remains of A4
    on this path is listed below. See [the security argument](V3-SECURITY-ARGUMENT.md).
- **Residual:** the adapter Rust itself is not proved. On the pre-commit
  path what remains reviewed and tested, not proved, is:
  - that the adapter acts on the verified results as `HookRun` and the
    models `hookPlan`/`hookEntry` say (it builds entries from
    `listing_fields`, iterates the flagged positions, and its per-entry
    check is at least as strict as `hookEntry`);
  - the rewrite of `ls-tree` records to index records (`tree_record`, A20);
  - sizing `ends` by the listing's NUL count (fails closed: the parse then
    refuses);
  - the equality of the staged `.transcrypt/config` blob with the
    configuration used;
  - reading exactly the announced object size and the trailing LF (A21);
  - building the stored key's primitives from the file's key bytes (A17);
  - finding the commits being brought in (A23);
  - the extra refusals for unprotected entries (a record moved to an
    unprotected name, a file that lost its protection), which look up old
    blobs by path in adapter code; they only refuse, and match `audit`.
- **Next reduction:** a verified `ls-tree` record parser (removing the
  `tree_record` rewrite), and moving the unprotected-entry checks onto
  `held_entries`.
- **Status:** narrowed; PROVED (source-derived inputs, model) + REVIEWED + TESTED.

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
  Plaintext buffers are not `mlock`ed. An optional idle limit
  (`unlock --private --timeout=…`, sent over the startup pipe) makes the
  agent forget the key; without it, the key lives until `lock` or logout.
- **Next reduction:** a separate UID or OS keyring if the threat model ever
  admits hostile same-UID code.
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
- **Evidence (selection loop):** the whole answer is parsed by the
  verified `parse_attr_response` (`parse_attr_response_spec`,
  `parse_attr_response_complete`); the adapter only builds the request
  (NUL-free paths, each NUL-terminated) and runs Git. For the index (the
  hooks, `verify-index`, `hydrate`, `lock`) the answer is checked against
  the listing's own paths by `parse_listing_attrs`
  (`parse_listing_attrs_spec`, both directions), so the request
  construction is no longer trusted there; `first_unselectable` refuses a
  selected symlink, submodule or reserved path.
- **Pattern hygiene:** `protect` refuses patterns that select nothing
  (directories, `./`, negation) and requires a pattern naming an existing
  file to select it.
- **Status:** parsing and path policy PROVED; Git's evaluation ASSUMED (A19);
  TESTED end to end.

### A17 — Stored key (the default unlock)

- **Claim:** `unlock` stores the Argon2id-derived key, never the
  passphrase, only in `$GIT_COMMON_DIR/transcrypt-v3/key`. That is a regular
  file of the public config it unlocks followed by the key (119 bytes), mode
  0600, in a 0700 directory owned by the user, outside `git config`. The key
  is used for the worktree config only if that config equals the stored one
  and authenticates with it; otherwise (a pulled rekey) the worktree counts
  as locked. Smudge also opens records that name the stored config (a
  checkout writes files before the config). The ciphertext does not depend
  on the mode.
- **Trust boundary:** our `credential.rs`; the local file system; Git's
  common directory for worktrees.
- **Consequence if false:** a key in public or shared state; a key used for
  another config (records under the wrong config, refused later by
  verification); different ciphertext per mode.
- **Evidence:**
  - PROVED: the decision is the verified `stored_key_state`
    (`stored_key_state_spec` = `storedKeySpec`: `Unlocked` only for a
    119-byte file holding exactly the current config whose key
    authenticates it, `storedKeySpec_unlocked`); composed with
    `authenticate_config` in `stored_key_authenticates_current_config`. A
    damaged file is refused by every command except `unlock`, which
    replaces it (fixed 2026-10-26; it used to refuse as well).
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
  - Rebinding requires a local change: the staged blob differs from
    `HEAD`'s at that path and is not a file of an incoming commit
    (`MERGE_HEAD`, `CHERRY_PICK_HEAD`, `REVERT_HEAD`, `REBASE_HEAD`); during
    a rebase or `am` without a known commit nothing is repaired. The source
    is a `HEAD` path whose index entry is gone or replaced, and the record
    must open there.
  - A record moved to an *unprotected* name is refused by `check_index` and
    the keyless audit (it would never be decrypted there).
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
  that does not already open is ever repaired). Its inputs are verified
  too: membership in `HEAD` and the incoming commits (`held_entries`), the
  local-change input (`is_local_change` = spec `LocalChange`) and the move
  sources (`next_move_source` = spec `MoveSource`, first at or after an
  offset, tried in `HEAD` order). `hook_repairs_only_local_changes`
  composes them: whatever the hook seals or rebinds is a `LocalChange`, and
  a rebind re-encrypts only a record that authenticates at a `HEAD` path it
  was moved from. Remaining: the sequencing state (A23), Git's listings
  (A20), and the adapter's call sequence (A4).
- **Status:** decision and inputs PROVED; TESTED + REVIEWED.

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
- **Hardening:** v3 runs its attribute queries with
  `core.ignorecase=false`, so selection never depends on the file system;
  while a v3 config exists, the top-level `.gitattributes` must define the
  `transcrypt` macro (hook, audit, doctor).
- **Residual (ACCEPTED):** local override files apply only locally: a
  `filter` rule in `.git/info/attributes` or the global attributes file can
  unprotect a file in this checkout, so local checks pass while a server
  audit (without those files) refuses the plaintext. `doctor` fails on such
  files and the pre-commit hook warns.
- **Status:** TESTED; overrides ACCEPTED RISK (an informed user's choice).

### A20 — Git's listings (new)

- **Claim:** `git ls-files --stage -z` prints the index being committed
  exactly: one `mode SP oid SP 0 TAB path` record per stage-0 entry, each
  NUL-terminated, raw path bytes, nothing else. `ls-tree -r -z` prints a
  commit's tree, which the adapter rewrites record by record
  (`tree_record`) to the same shape.
- **Trust boundary:** Git; the adapter's `tree_record` rewrite (reviewed,
  fuzz-tested in `git_output_parsers_never_panic_and_accept_only_exact_records`).
- **Consequence if false:** the hook would check entries other than those
  Git commits.
- **Evidence:** TESTED by every lifecycle suite (raw and non-UTF-8 paths,
  TABs and newlines in names); the parse PROVED both ways
  (`parse_listing_spec`), so a listing of any other shape is refused.
- **Status:** TESTED; parsing PROVED.

### A21 — Object replies (new)

- **Claim:** `git cat-file --batch` answers the requested object id, with
  the header `<oid> SP blob SP <size> LF`, then exactly `size` bytes and an
  LF; the adapter reads exactly those bytes.
- **Evidence:** the header must be exactly `BatchHeader` for the requested
  id with a canonical decimal size (`parse_batch_header_spec`; the size is
  unique, `batchHeader_unique`); only sizes within the record bound are
  read (`blob_read_spec`); the trailing LF is checked and a failed read
  discards the reader. TESTED (`git_output_parsers_never_panic_and_accept_only_exact_records`,
  all lifecycle suites).
- **Residual:** the read of exactly `size` bytes (adapter I/O).
- **Status:** header PROVED; content read TESTED.

### A22 — The commit is the checked index (new)

- **Claim:** Git records the index the `pre-commit` hook checked last
  (after the hook's own `update-index`, Git re-reads the index), and nothing
  else changes it before the commit is written.
- **Consequence if false:** an index checked by the hook would differ from
  the one committed (the audit still checks history, A13).
- **Evidence:** TESTED by every pre-commit test, including commits with
  sealing; a concurrent writer of the same index is outside the threat
  model (same-UID, A8).
- **Status:** TESTED; ASSUMED (Git's commit flow).

### A23 — The commits being brought in (new)

- **Claim:** during a merge, cherry-pick, revert or rebase, `MERGE_HEAD`,
  `CHERRY_PICK_HEAD`, `REVERT_HEAD` and `REBASE_HEAD` name the commits whose
  content the index may hold; while a rebase or `am` runs without such a
  commit, the hook treats nothing as local.
- **Consequence if false:** content of a commit could be treated as a local
  change and repaired (re-encrypted), i.e. laundered.
- **Evidence:** TESTED (`merges_are_verified_before_the_merge_commit`,
  hostile move in `git_lifecycle`, rebase and cherry-pick suites).
- **Status:** TESTED.

## Ranked unresolved risks and *product* opportunities

Ranked by violation of [the declared product promise](V3-PRODUCT-CHARTER.md),
realistic impact and effort.

1. **External crypto/adapter review** (A5/A9/R-01): required for credible
   release claims. Differential vectors reduce, but do not discharge, the
   trusted-library boundary.
2. **Adapter correctness** (A4/A7/A8/A16): the decisions and, on the
   pre-commit path, their inputs are proved (selection, rebind inputs,
   stored key, object replies; [security argument](V3-SECURITY-ARGUMENT.md));
   the adapter's call sequence and I/O remain reviewed and tested. Next
   targets: an `ls-tree` record parser, the unprotected-entry checks, and
   the smudge/hydrate inputs.
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
| Parsing Git's attribute answers (what is protected) | `parse_attr_record_spec` (both directions), `parse_attr_response_spec`, `parse_attr_response_complete` |
| Smudge keeps only genuine envelopes; opens only its own config | `smudge_action_spec`, `smudgeSpec_keep_envelope`, `smudgeModel_spec` |
| The pre-commit hook repairs only local changes | `seal_action_spec`, `sealSpec_repairs_only_local`; inputs: `held_entries_spec`, `is_local_change_spec`, `next_move_source_spec`; composed in `hook_repairs_only_local_changes` |
| Git listings are parsed exactly; each entry's fields | `parse_listing_spec` (both directions), `listing_fields_spec` |
| Selection checked against the listing's own paths; selectability | `parse_listing_attrs_spec` (both directions), `first_unselectable_spec` |
| Keyless move check | `blob_elsewhere_spec` |
| Stored-key decision | `stored_key_state_spec`, `storedKeySpec_unlocked`, `stored_key_authenticates_current_config` |
| `cat-file --batch` reply framing | `parse_batch_header_spec`, `batchHeader_unique`, `blob_read_spec` |
| End to end: the hook accepts only authenticated ciphertext at the selected paths | `hook_accepts_only_authenticated_ciphertext` (with `hookPlan_spec`) |
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
| Key loading | `stored_key_state` (with `authenticate_config` under the stored key), or agent `Ping` | stored key file (config ‖ 64-byte key); current config | `Unlocked`; `unlock` replaces a `Damaged` file |
| Protected-file selection | `parse_attr_response` over the whole answer (one record per requested path, in order, nothing else); `is_reserved_path` | raw paths sent to `check-attr -z --stdin filter` (`--cached`, worktree, or a commit's temporary index) | `protected = true` |
| Pre-commit re-encryption (`seal_staged`) | `seal_action` on (`open_record` at its path, `is_local_change` over `held_entries` in `HEAD` and the incoming commits, `parse_file_header`, `open_record` at a `next_move_source` path), then `clean_file`/`seal_record` at the new path | staged blobs by oid; `HEAD` and incoming listings (`parse_listing`); sequencing state | `Seal` or `Rebind` only |
| Agent framing | `encode_frame_header` / `decode_frame_header`, `encode_be_u32` / `decode_be_u32` | opcode, config, lengths | proved roundtrip |
| Git filter-process framing | `decode_pkt_len` for every packet; then the same conversion as the per-file filters | 4-byte pkt-line headers from Git; `command=`/`pathname=` values | `Ok` (else the process ends and Git fails) |
| Agent dispatch | `authorize_agent_request` before the body is read; peer UID check | opcode, supplied config, startup config, path, length | `Ok(op)` from a same-UID peer |
| Agent startup | `authenticate_config` | config bytes, piped key | `Ok` |
| `unlock` / `init` | `authenticate_config` / `initialize_config` | config bytes / fresh salt | `Ok`, before any persistent effect |
| Index and tree listings | `parse_listing` (whole listing: records, object ids), then `listing_fields` per entry | `ls-files --stage -z`, or `ls-tree -r -z` records rewritten to that shape (path copied verbatim) | `true` (else refuse) |
| Object reads | `is_object_id`, then `parse_batch_header` and `blob_read` | oid from the parsed snapshot | `true`; one `cat-file --batch` per process; header exactly `<oid> blob <size>` (canonical decimal), `Read` only within 16 MiB, trailing LF checked |
| `verify-index` and the hook's check | `parse_listing_attrs`, `first_unselectable`, then `open_record` per entry (incremental hook: unless `held_entries` shows it unchanged since `HEAD` and `HEAD^1`), or, while locked, `record_envelope_ok` and `blob_elsewhere` | snapshot listing; blobs by oid | `true` / `Ok` for every entry |
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
