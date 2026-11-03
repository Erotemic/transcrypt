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
assumptions of the pre-commit path. A24 (2026-10-26) names what the
incremental hook trusts about history; on 2026-11-01 its induction over
keyed commits was proved, leaving the commit-step and policy contracts and
the start of history assumed; on 2026-11-02 it was restated without
selection (`RecordsAuthentic`), which removed the selection contract (A19's
local attribute sources) from the history, and the hook's per-entry check
moved into the core (A4). Later on 2026-11-02 the keyed audit was made to
keep the same invariant for history the hook never saw (its per-entry check
`audit_check` in the core, the single-commit theorem in `Audit.lean`), so it
establishes the start of A24 (A13). A25 (2026-10-28) names the per-platform
OS adapters (Unix and Windows). Older security-hardening priorities are
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
| A4 | Adapter invokes the core correctly and obeys it | Narrowed: structural (object-id snapshot, stamps, literal Git paths) + PROVED (model, incl. the end-to-end hook theorems) + REVIEWED + TESTED; the hook's inputs, each entry's check (`staged_check`), its acceptance (`staged_verdict`) and the loop over every index entry (`index_verdict`, `index_verdict_accepts`) are verified functions; what remains on the hook's check is one call (`HookAccepted`: the run's inputs, refuse unless `Ok`) and the evidence's answers about each entry's own blob and path (`HookAnswers`) |
| A5 | `Keyed` realizes the primitive contract | TESTED (differential vs OpenSSL, exhaustive tampering) |
| A6 | Private-mode credential agent relays core results faithfully | TESTED + REVIEWED; same-UID ACCEPTED RISK (optional mode) |
| A7 | Git semantics | TESTED on Git 2.43; ASSUMED otherwise |
| A8 | OS / filesystem behavior | Narrowed + TESTED (SIGKILL fault injection); same-UID races ACCEPTED RISK |
| A9 | RustCrypto implementations are correct | TESTED (differential); no external audit |
| A10 | AES-SIV, Argon2id, SHA-256 security | ASSUMED (standard) |
| A11 | A Git object id names exactly one content | ASSUMED (Git's hash) |
| A12 | File stamps change on modification; v3 processes honor the staging lock | TESTED |
| A13 | History is audited before it reaches others (deployment) | REVIEWED + TESTED; depends on deployment. What a keyed audit of one commit establishes is PROVED (model) (`keyed_audit_authenticates_commit`: records and selection authenticate given the parent's; the per-entry check `audit_check` is source-derived); the keyless audit checks envelopes only (`keyless_audit_checks_envelopes`) |
| A14 | Keyless envelope checks only stop accidental plaintext | ACCEPTED RISK (by design) |
| A15 | Git creates worktree files with the umask its filters inherit | TESTED (Git 2.43; CI 2.34, Apple Git); private mode only |
| A16 | Git-attribute selection: every decision uses Git's own answer for the exact path | Parsing PROVED (against the listing's own paths); selection by Git ASSUMED (A19); TESTED end to end |
| A17 | The stored key is local-only, used only for the config it authenticates and with its own check value, with primitives built from exactly its bytes, and mode-independent | Selection, pairing and the check value PROVED relative to the key-schedule contract (`unlock_stored_key_spec`, `authenticate_key_spec`, `key_check_opens_spec`, `stored_key_binds_file_operations`; `ValidatedKey` is the only file-operation interface); that the check value detects damage to either key half ASSUMED (A10, the cipher's property) and TESTED for every bit; key schedule TESTED (A5); file I/O TESTED + REVIEWED; local-account exposure ACCEPTED RISK (by charter) |
| A18 | Path-bound renames are re-encrypted for the new path, never laundered | Decision and inputs PROVED (`repair_plan`, `needs_record`, `entry_provenance`, `next_move_source`, `hook_repairs_only_local_changes`, `hook_skips_only_unrepairable`); TESTED (real Git) + REVIEWED |
| A19 | Git evaluates `filter` the same way for its filters, `check-attr --cached` and a commit's attribute files | TESTED (Git 2.43; CI 2.34); local override files ACCEPTED RISK (they can unprotect a file locally); no longer a hypothesis of the A24 history (2026-11-02) |
| A20 | Git prints its index and tree listings exactly (`ls-files --stage -z`; `ls-tree -r -z`, rewritten record by record), in byte order of paths, each path once | TESTED; parsing and order PROVED (`parse_listing_spec`: anything else is refused) |
| A21 | `cat-file --batch` answers the requested object, and the adapter reads exactly the announced content | Header and read decision PROVED (`parse_batch_header_spec`, `blob_read_spec`); content read TESTED |
| A22 | Git commits the index the pre-commit hook checked last | TESTED; ASSUMED (Git's commit flow) |
| A23 | The sequencing state names the commits being brought in (`MERGE_HEAD`, `CHERRY_PICK_HEAD`, `REVERT_HEAD`, `REBASE_HEAD`, rebase directories) | TESTED (merge, octopus, cherry-pick, rebase suites) |
| A24 | The history the incremental pre-commit hook trusts was checked: `HEAD`'s records authenticate at their paths (`RecordsAuthentic`, selection-independent) | Narrowed: use PROVED (model) (`hook_records_authentic`, `keyed_check_records_authentic`); the induction over keyed commits PROVED (model) with no policy or selection hypothesis (`keyed_history_authenticated_by_guard`, `config_unchanged_of_guard`, `records_authentic_of_checked_commit`); remaining: the commit step (A22, A11) and the start of history, now discharged by a keyed audit of the commit `HEAD` names (`audited_head_starts_keyed_history`, PROVED (model)) or a full keyed check; what remains of the start is the audit's own: its first commit's parent records when that parent lies outside the audited range (A13) |
| A25 | Each platform's OS adapter (`fsat*.rs`, `os_*.rs`) provides the primitives A6, A8, A12 and A17 name | TESTED: the whole suite on Linux, FreeBSD 14.5, NetBSD 10.1, OpenBSD 7.9 and Windows Server 2025 (non-administrator); macOS not yet run (its CI jobs have not been seen passing); REVIEWED |

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
  `Classical.choice`, `Quot.sound`. Every declaration the proofs depend on,
  mathlib's included, is replayed from scratch through the kernel
  (`leanchecker --fresh`) on five systems: Linux, Windows, FreeBSD, and
  NetBSD and OpenBSD with Lean built from source under a runtime and
  build-flag port (`proofs/aeneas/ports`), so a kernel or `.olean` fault
  specific to one build or platform would have to recur on all of them.
- **Residual:** a translator bug that tests happen not to exercise.
- **Next reduction:** differential execution of the extracted definitions
  once they can be made computable.
- **Status:** ASSUMED.

### A4 — Adapter-to-core correspondence

- **Claim:** the effectful adapter (every module of
  `rust/crates/transcrypt-rs/src/` other than the core) passes the core the right bytes (exact Git path, on-disk config,
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
    `held_entries`, `entry_provenance`, `needs_record`, `repair_plan`,
    `next_move_source`, `blob_elsewhere`;
    object replies are framed by `parse_batch_header` and `blob_read`; the
    stored key by `stored_key_state`. The end-to-end theorems
    (`hook_accepts_only_authenticated_ciphertext`,
    `hook_repairs_only_local_changes`, `hook_skips_only_unrepairable`,
    `stored_key_authenticates_current_config`) take the adapter's observed
    results of these calls as hypotheses (`HookEvidence`; for the repairs,
    `RepairInputs` with `RepairContracts`), so what remains of A4
    on this path is listed below. See [the security argument](V3-SECURITY-ARGUMENT.md).
  - **PROVED (typed repair plan, 2026-11-01).** The pre-commit repair is
    decided by the core on typed values, not four positional booleans from
    different domains. The core derives each entry's `Provenance`
    (`Committed`, `Local`, `Forced`, `Unknown`) from the snapshot bytes in
    one call (`entry_provenance` = spec `ProvenanceIs`), says whether its
    blob is read at all (`needs_record`; `hook_skips_only_unrepairable`: a
    skipped entry is neither the user's change nor forced), and decides
    `repair_plan(Provenance, RecordClass)` = spec `repairSpec` (a complete
    result, `Rebind` naming the `HEAD` record it re-seals from). So the
    adapter no longer computes the local-change input from its own arrays,
    nor orders booleans for the decision (a swapped argument does not
    typecheck); the end-to-end statement reasons about the generated
    `entry_provenance`, `needs_record` and `repair_plan` directly.
  - **PROVED (settled guard, 2026-11-01).** Whether the incremental hook
    may count any entry as settled (skip authenticating it) is no longer
    adapter code: the core's `policy_unchanged`, over the verified index,
    `HEAD` and `HEAD^1` listings, compares their records at policy paths
    (`is_policy_path`: every attribute file, top-level or nested, by the
    core's `is_attributes_path`, and `CONFIG_PATH`), mode and object id
    included. `policy_unchanged_spec` proves it equal to the spec's
    `PolicyUnchanged` (the three `policyEntries` lists are equal; no
    order or uniqueness assumed), and `policy_unchanged_sound` gives what
    the history argument consumes: when it returns `true` the three
    snapshots hold exactly the same entries at every attribute file and at
    the config (`PolicyUnchanged.agree`, `PolicyUnchanged.holds`). It
    compares committed bytes; it does not interpret the attributes. The
    adapter's reimplementation (`lifecycle::policy_unchanged`,
    `is_attributes_file`) is deleted; its `.transcrypt/config` constant is
    the core's.
  - **PROVED (per-entry check, 2026-11-02).** The hook's final check of
    every index entry, protected or not, is decided by the core: each
    position is `staged_check` followed by `staged_verdict` (since the next
    item, inside the extracted loop `index_verdict`). The core
    decides which check an entry gets (`staged_check`, `staged_check_spec`
    = `StagedCheckOf`: a protected entry as `entry_check` says, settled
    only under the guard and when `HEAD` and `HEAD^1` hold its exact
    record, `held_records`, `held_records_spec`; an unprotected file staged
    since `HEAD` must be no record; one `HEAD` holds is authenticated if it
    is a record unless the incremental hook trusts `HEAD` under the guard),
    whether the blob is read (`reads_blob`), and whether the entry passes
    (`staged_verdict`, `staged_verdict_ok` = `VerdictOk`). The verdict asks
    the adapter three questions through the trait `StagedEvidence`, each only
    when its check needs it (visible in the extracted code, not a theorem;
    tested by `staged_verdicts_accept_only_what_their_check_requires`):
    `is_record`, `opens`, `elsewhere`, each about the position it is asked
    for. The earlier handwritten acceptance
    model (`hookEntry` with its own `open_record` call and `EntryAccepted`),
    the adapter's conjunction `settled = same_policy && in_head[i] &&
    in_parent[i]`, and the adapter's refusal of a record staged at an
    unprotected name are gone: all three are the core's now.
  - **PROVED (the hook's loop, 2026-11-02).** The loop over the index is
    the core's `index_verdict`, which the hook calls once
    (`Listing::index_verdict`, with the snapshot's own bytes and ends):
    `index_verdict_accepts` proves that if it returned `Ok`, every position
    of the listing, in order, was checked by `staged_check` with the run's
    `flags`, `in_head`, `in_parent`, `keyed`, `incremental` and guard, had
    its blob read for that position exactly when `reads_blob` says so, and
    passed `staged_verdict` (`PositionAccepted`); the first refusal stops it.
    The answers are fallible in their type (`Option<bool>`): an answer the
    adapter could not find is `None`, which the verdict refuses
    (`StagedRefusal::Unanswered`), as is a failed read. So the adapter no
    longer iterates positions, chooses whether to read, or decides that a
    failed read refuses (earlier a `failure` cell the adapter checked after
    each verdict); the handwritten Lean loop `hookPlan` and its per-entry
    list `HookChecks` are gone.
  - **PROVED (audit per-entry check, 2026-11-02).** The audit's check of
    each examined entry of a commit is the core's `audit_check`
    (`audit_check_spec` = `AuditCheckOf`), in the hook's vocabulary, decided
    by the same `staged_verdict`; the Lean model `auditPlan` only sequences
    the two (`Audit.lean`). The adapter's earlier separate checks (the
    protected-record loop, the move-away refusal) are gone; what remains
    adapter code there is the drift check (`check_drift`, refuse-only) and
    the policy checks.
- **Residual:** the adapter Rust itself is not proved. On the pre-commit
  path what remains reviewed and tested, not proved, is:
  - the one call of the hook's check (`HookAccepted`, `HookEvidence`):
    `check_staged` calls `index_verdict` once, with the parsed index
    snapshot (its own bytes and ends, through `Listing`), the run's `flags`
    (`parse_listing_attrs`), `in_head` and `in_parent` (`held_records`),
    `key.is_some()`, `incremental`, the guard (`policy_unchanged`) and the
    id of the configuration it compared with the staged
    `.transcrypt/config`, and refuses the commit unless it returns `Ok`;
  - the evidence (`HookAnswers`, `IndexEvidence` in `check_staged`), in
    every state the run passes through (`HookAnswersIn`'s `good`, kept by
    `read`), about position `i`'s own entry: `read(i)` reads that entry's
    blob by its object id and `blob` returns it (A11, A21); `is_record(i)`
    is `record_envelope_prefix_ok` of the blob's size and first
    `ENVELOPE_PREFIX_LEN` bytes (A21 for the bytes); `opens(i)` is
    `Key::open` at the entry's path (the core's `open_record` with the stored
    key's primitives, A17, A5; in private mode the agent's call of the same
    function, A6), on the blob `read` read for `i` or one read for it;
    `elsewhere(i)` is the verified `blob_elsewhere` on the run's ordered
    listings; each is `None` exactly when it could not be found;
  - on the audit path (`audit_commit`, `check_entries`): the facts passed
    to `audit_check` (`AuditContracts`: `held` is "not listed by
    `diff-tree`", `moved` is "the blob of a path `diff-tree` lists as
    deleted", `selected` is `check-attr` against the commit's attribute
    files, A19, A20), the choice of `AuditBase` (`Parent` only when
    `diff-tree` does not list the config), the three answers
    (`AuditAnswers`: `elsewhere` is `moved`), and the checked-record cache
    (`settled_by_cache`);
  - the rewrite of `ls-tree` records to index records (`tree_record`, A20);
  - sorting the object orders (`Listing::object_order`; a wrong order is
    refused by the verified `object_order_ok`, so this only fails closed)
    and merging the incoming trees by path (`Listing::merge`, parsed with
    `unique = false`);
  - sizing `ends` by the listing's NUL count (fails closed: the parse then
    refuses);
  - the equality of the staged `.transcrypt/config` blob with the
    configuration used;
  - reading exactly the announced object size and the trailing LF (A21);
  - building the stored key's primitives from the file's key bytes (A17);
  - finding the commits being brought in (A23);
  - the refusal of a file that lost its protection to another named
    filter (`check_drift`), which looks up old blobs by path in adapter
    code; it only refuses, and matches `audit`;
  - for the repairs, the evidence about each blob: that the `RecordClass`
    `classify` reports is what `RecordEvidence` states (it tries the key at
    the entry's own path, then reads the header, then tries the move
    sources `next_move_source` yields, in order: `OpensHere`, `Plaintext`,
    `MovedFrom(j)` with the plaintext opened at `HEAD` record `j`, or
    `Unusable`), that it reads the blob only when `needs_record` says so,
    and that it executes exactly the plan (`Seal`: the staged plaintext;
    `Rebind(j)`: that plaintext; `Keep`/`Leave`: nothing); and that it
    lists the incoming commits whenever a protected entry is not in `HEAD`
    (`RepairContracts.lazy`).
- **Next reduction:** a verified `ls-tree` record parser (removing the
  `tree_record` rewrite), and moving the drift check onto the core.
- **Status:** narrowed; PROVED (source-derived inputs, model) + REVIEWED + TESTED.

### A5 — `Keyed` realizes the primitive contract

- **Claim:** `Keyed` computes RFC 5297 AES-256-SIV with AD vector
  `[domain, config, path]` (three S2V components, not a concatenation),
  SHA-256 truncation, exact output lengths, and never reports false success.
  These are the clauses of Lean's `Realizes`. Since 2026-11-02 the
  stored-key and key-use theorems take it per key: `KeyScheduleRealizes`
  states that `Keyed::from_key(k)` (the core's `V3KeySchedule`) realizes the
  suite of exactly the bytes `k` (A17).
- **Trust boundary:** `transcrypt-rs/src/lib.rs` plus A9.
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
- **Trust boundary:** our `session.rs`; Unix-domain sockets (also on
  Windows, A25); process isolation.
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
  core-dump/ptrace controls work. (The Windows counterparts are A25.)
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
  - The stamp (device, inode, size, mtime to the nanosecond) cannot see an
    edit of the same size within one tick of the file system's clock
    (10 ms on OpenBSD, coarser on a VM missing ticks), nor, within that
    tick, a file replaced by another of the same size where the file system
    reuses the freed inode number (OpenBSD does).
  - Hard links to a plaintext file survive `lock`.
  - Root; hibernation and swap of non-key buffers. On Windows, a private
    directory may also grant LocalSystem and Administrators, who can read
    any file anyway (the counterpart of root).
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
  Object ids the adapter receives for blobs it writes (`git fast-import`
  `get-mark`, through `IndexUpdate`) are not trusted for security: the
  hook's final check and `verify-index` read every staged protected blob
  back by id and check it, so a wrong id fails closed.
- **Status:** ASSUMED.

### A12 — Stamps and the staging lock (new)

- **Claim:** any write, truncation or replacement of a file changes its
  (device, inode, size, mtime) stamp. All v3 processes take the exclusive
  lock on `.git/transcrypt-v3-staging` before mutating the worktree.
- **Consequence:** a concurrent edit between check and replace is lost.
- **Evidence:** TESTED (`replacement_refuses_a_file_changed_since_it_was_checked`,
  concurrent-entry refusal), on Linux and FreeBSD. ctime is deliberately
  not part of the stamp: FreeBSD's UFS soft updates change a renamed file's
  ctime asynchronously, hundreds of milliseconds after the rename (found by
  the FreeBSD run of the end-to-end suite, where every `lock` right after a
  `hydrate` was refused).
- **Residual:** filesystems with coarse timestamps *and* writes that
  preserve size and inode within one tick; a same-UID program that writes in
  place and then restores the mtime (`touch -r`); a chmod between check and
  replace (the replacement takes the mode read just before it is written);
  non-v3 writers do not take the lock.
- **Status:** TESTED.

### A13 — History is audited before others rely on it (new, deployment)

- **Claim:** plaintext committed where no v3 filter ran never reaches a
  shared remote. Examples: a clone that never ran `unlock`, merges and
  rebases that skip `pre-commit`, `--no-verify`.
- **Trust boundary:** the installed `pre-push` hook, or `transcrypt-rs audit`
  in CI or a server-side hook.
- **Consequence:** plaintext published.
- **Evidence:** TESTED (pre-push refuses a `--no-verify` plaintext commit; a
  keyless `audit` in a never-unlocked clone refuses its plaintext commit).
- **What a keyed audit establishes (2026-11-02).** The audit checks each
  commit against its first parent: the entries `diff-tree` lists, or the
  whole tree for a root commit, a config change or an attribute change.
  Each examined entry is checked by the extracted `audit_check`
  (`audit_check_spec`) and `staged_verdict` (`staged_verdict_ok`), the
  pre-commit hook's vocabulary. With the key: a selected entry
  authenticates at its path; an unprotected file the parent holds exactly
  is trusted from the parent while the config is unchanged
  (`AuditBase.Parent`); every other unprotected regular file is read as far
  as its envelope prefix and, if it is a record of the commit's config,
  must authenticate at its path (a forgery or a moved record is refused, a
  genuine record at its own unprotected path passes). PROVED (model,
  `Audit.lean`): `keyed_audit_authenticates_commit` (the commit's
  `RecordsAuthentic` given the parent's when it trusted the parent, nothing
  for `AuditBase.Tree`; and its `SelectionAuthentic` given the parent's
  selection, `AuditSelectionAgrees`), `audited_head_starts_keyed_history`
  (an audited `HEAD` is the start condition of
  `keyed_history_authenticated_by_guard`),
  `audited_head_keyed_history_authenticated` and
  `keyed_audit_chain_authenticated` (a chain of audits, each commit's
  parent the previous one). Contracts: `AuditContracts` (A20's diff
  contract, A19, A11, A21), `AuditAnswers` (A4), `Realizes` (A5). TESTED:
  `the_keyed_audit_authenticates_records_at_unprotected_paths`,
  `the_audit_authenticates_a_copied_record_at_its_new_path`,
  `the_audit_trusts_no_parent_across_a_config_change`,
  `audits_read_no_unchanged_unprotected_file`,
  `local_attribute_overrides_never_admit_a_forged_record_through_checked_history`.
- **Keyless audit (by design, A14).** Without the key the audit checks
  envelopes: every examined selected entry is a regular file with the
  config's envelope that the parent holds or that is no blob of a path the
  commit deleted (`keyless_audit_checks_envelopes`); an unprotected file is
  refused only when it is a moved record. It authenticates nothing, and its
  output says so ("envelopes only: unlock to authenticate them and any
  record at an unprotected path").
- **Trusted parents and the cache.** A first parent outside the audited
  range (`--not origin/main`, the pre-push and pre-receive ranges) is
  trusted: its records are assumed to authenticate (it was audited when it
  was pushed, or is deliberately excluded). An audit from the root
  (`transcrypt-rs audit`, default `HEAD`) trusts nothing. Within a run the
  adapter checks each (blob, config, path) once (`settled_by_cache`): an
  entry is recorded only after a selected entry's check passed, under a
  config whose key is fixed for the run, and settles only `Authenticate`
  and `Envelope`; reviewed and tested
  (`the_audit_authenticates_a_copied_record_at_its_new_path`), not modelled.
- **Cost:** prefix reads only for changed unprotected files (whole tree only
  for a root commit or a config change); an unprotected file the parent
  holds is never read, even across an attribute change
  (`audits_read_no_unchanged_unprotected_file`).
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
  (`record_envelope_ok_spec`), decided by the size and first `FILE_MIN_LEN`
  bytes alone (`record_envelope_prefix_ok_record`). It rejects every accidental plaintext, since
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
  file of the public config it unlocks, the key, and the key's check value
  for that config (158 = 55 + 64 + 39 bytes), mode
  0600, in a 0700 directory owned by the user (on Windows, an owner-only
  DACL: A25), outside `git config`. The key
  is used for the worktree config only if that config equals the stored one
  and authenticates with it, and the check value opens under it; otherwise
  (a pulled rekey, or a damaged file) the worktree counts as locked. Smudge also opens records that name the stored config (a
  checkout writes files before the config). The ciphertext does not depend
  on the mode. Every file operation uses primitives built from exactly the
  key bytes that authenticated the configuration it is paired with.
- **Trust boundary:** our `credential.rs` and `ValidatedKey`/`Keyed` in
  `lib.rs`; the local file system; Git's common directory for worktrees.
- **Consequence if false:** a key in public or shared state; a key used for
  another config (records under the wrong config, refused later by
  verification); different ciphertext per mode.
- **Evidence:**
  - PROVED (relative to the key-schedule contract `KeyScheduleRealizes`,
    below): which key a configuration is used with is decided by the
    verified core. `authenticate_key` (`authenticate_key_spec`) builds the
    primitives from the given key bytes and returns them only if the
    configuration authenticates under them. `unlock_stored_key`
    (`unlock_stored_key_spec`, `StoredUnlock`) returns primitives only for a
    present 158-byte file whose first 55 bytes are the current config; the
    primitives are those of exactly the next 64 bytes (`storedKeyBytes`),
    returned together with the config they authenticated (the current
    config's bytes), and the last 39 bytes are their check value for that
    config (`storedKeyCheck file = keyCheckValue`: the suite's sealing of
    the constant `transcrypt/v3/key-check` at the reserved path
    `.transcrypt/key-check`, a path no record may have,
    `keyCheckPath_reserved`); otherwise the `storedKeySpec` state, never
    `Unlocked`. The check value is decided by the verified
    `key_check_opens` (`key_check_opens_spec`: it accepts exactly
    `keyCheckValue`, sound and complete) and written by the verified
    `seal_key_check` (`seal_key_check_spec`), so what `store` writes is
    accepted (`key_check_round_trip`). `stored_key_binds_file_operations`
    takes that output as its premise (no longer an arbitrary `Realizes`
    instance plus an independent `authentic` flag) and concludes that every
    record opened or sealed with those primitives is bound to that config
    and path under the suite of the file's key bytes. The older decision
    theorems remain (`stored_key_state_spec` = `storedKeySpec`,
    `storedKeySpec_unlocked`, `stored_key_authenticates_current_config`). A
    damaged file is refused by every command except `unlock`, which
    replaces it (fixed 2026-10-26; it used to refuse as well).
  - Structural (2026-11-02): files are sealed and opened only through
    `transcrypt_rs::ValidatedKey`, whose fields are private (a
    `compile_fail` doc test) and whose constructors are only the verified
    `authenticate_key` (`authenticate`, `unlock`, `initialize`) and
    `unlock_stored_key` (`from_stored`). The stored key, `unlock`, `init`,
    `migrate`, `rekey`, `reencrypt` and the private agent hold that type;
    the free functions taking a config and a key separately are gone.
    `tests/key_boundary.rs` fails if adapter code outside `lib.rs` names
    `Keyed`, the primitive traits, `derive_key` or the core's sealing,
    opening or key functions.
  - TESTED: key files of another repository, a file naming this config
    with another repository's key, one naming another config with this
    key, this config and key with another key's check value, and this file
    with one bit flipped in the S2V half of the key, in its CTR half or in
    its check value are all stale; nothing is encrypted with them, nothing is decrypted
    (also by a checkout, which uses the config the file names), and the
    private agent refuses to start with another repository's key
    (`stored_keys_of_other_configs_are_never_used`); the stored-key choice
    against `stored_key_state` with a toy key schedule, including a file
    naming one config with a key that also authenticates the current one
    (`stored_keys_select_the_file_key_for_the_config_it_authenticates`);
    `ValidatedKey::from_stored` returns exactly the file's key bytes, the
    file `to_stored` writes reads back to the same key, and every
    single-bit change of the key (both halves) or of the check value is
    stale (`stored_keys_validate_only_their_own_authentic_config`, all 824
    bits with the production AES-SIV); a file of the earlier layout
    (config and key, 119 bytes) is damaged and `unlock` rewrites it
    (`legacy_keys_macro_redefinitions_and_crlf`).
  - Written via an exclusive 0600 temporary, `fsync` and `renameat` in the
    held, checked directory; read with `O_NOFOLLOW`, exact size required.
  - `assert_unlocked` (git_lifecycle): exactly one private 64-byte key file,
    no agent, no passphrase in `.git/config` or the key file.
  - Stale key after a pulled rekey decrypts and encrypts nothing until
    `unlock` (`pulled_rekey_makes_the_stored_key_stale_until_unlock`).
  - Mode independence (`stored_and_private_modes_encrypt_identically`).
  - `lock` deletes it; `uninstall` deletes it.
- **Remaining assumptions (narrowed 2026-11-02):**
  - *Key schedule* (`KeyScheduleRealizes`, a visible hypothesis of the
    theorems above; A5 for every key): `Keyed::from_key(k)` holds exactly
    the bytes `k` (refusing any other length) and realizes the suite `σ k`
    of those bytes; `ValidatedKey::secret` returns the bytes the held
    `Keyed` was built from. TESTED (`Keyed::from_key` length refusals; the
    returned secret equals the file's key slice; A5's tests for the
    primitive under one key).
  - *File I/O*: the bytes `from_stored` receives are the key file's bytes
    and `store` writes exactly `ValidatedKey::to_stored`, `config ‖ secret ‖
    seal_key_check(config)` (REVIEWED, TESTED as above).
  - *Damage detection* (the unchecked CTR half found and closed
    2026-11-02): config authentication is the AES-SIV encryption of the
    empty plaintext, so it depends only on the S2V (CMAC) half of the key,
    bytes 0..32 (RFC 5297); a stored key with an altered CTR half used to be
    `Unlocked` and seal records the genuine key refuses. The check value is
    the encryption of a nonempty constant, so opening it decrypts with the
    CTR half and verifies the tag over the result with the S2V half. What
    is PROVED is that `Unlocked` implies the check value is the selected
    key's own (`keyCheckValue` of its suite). That a key differing in
    either half yields a different check value, so that damage is
    detected, is a property of AES-SIV (A10), ASSUMED; TESTED for every
    single-bit change. The private agent's key needs no check value: it
    comes from the parent's `ValidatedKey` through a pipe (whole or not at
    all) and never rests in storage.
  - *Earlier layout*: a key file written before the check value (config
    and key, 119 bytes) is `Damaged`: every command but `unlock` refuses it
    ("damaged .git/transcrypt-v3/key, or one an earlier build wrote; run
    `transcrypt-rs unlock` again"), and `unlock` replaces it. v3 is
    unreleased, so this one-time re-unlock replaces a migration.
  - *Provenance*: nothing proves that the stored key was derived by Argon2id
    from a passphrase (A9 tested by vectors, A10 assumed) or written by a
    particular `unlock`; the theorems are about whatever key bytes the file
    holds.
- **Residual (ACCEPTED, by the charter):** anything that can read the
  user's files (other same-UID programs, backups, copies of `.git`) can use
  the key, as it can read the unlocked plaintext. Deleting the file is not a
  secure erasure.
- **Next reduction:** none planned for the file's integrity. Private mode
  remains the stricter alternative for local exposure.
- **Status:** key selection and pairing PROVED relative to
  `KeyScheduleRealizes`, including that an unlocked key's check value is
  its own; that this detects damage to either half ASSUMED (A10) and
  TESTED; the key schedule TESTED (A5); file I/O TESTED + REVIEWED;
  local-account exposure ACCEPTED RISK.

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
- **Proof:** the decision itself is the verified `repair_plan` on a
  `Provenance` and a `RecordClass` (`repair_plan_spec` = spec `repairSpec`,
  `repairSpec_repairs_only_local`: only the user's content, or plaintext
  `protect` forced, that does not already open is ever repaired; only
  plaintext is sealed; only a record the user moved is re-sealed). The
  provenance is verified too: `entry_provenance` looks the entry up in
  `HEAD` and the incoming commits (= spec `ProvenanceIs`), and
  `needs_record` decides which blobs are read; the move sources are
  `next_move_source` (= spec `MoveSource`, first at or after an offset,
  tried in `HEAD` order). `hook_repairs_only_local_changes` composes them:
  whatever the hook seals or rebinds is the user's change (or forced
  plaintext, sealed), a `LocalChange`, and a rebind from `HEAD` record `j`
  re-encrypts only a record that authenticates at exactly that record's
  path, a place it was moved from; `hook_skips_only_unrepairable`: an entry
  whose blob is skipped is neither the user's change nor forced.
  Remaining: the sequencing state (A23), Git's listings (A20), and the
  adapter's evidence and execution of the plan (A4).
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
- **Not a hypothesis of the history (2026-11-02):** the history
  theorem used to assume Git's selection a fixed function of the committed
  policy entries (`SelectionByPolicy`), which `.git/info/attributes`,
  `core.attributesFile` and the system attributes contradict: they change
  the selection without changing a committed file. A24 now carries an
  invariant that does not mention selection (`RecordsAuthentic`), so the
  contract and its exclusion of local sources are gone. Each run still
  takes `GitAttributes` (its `check-attr --cached` answer is the selection
  Git's filters apply), which local sources do not affect.
- **Status:** TESTED; overrides ACCEPTED RISK (an informed user's choice).

### A20 — Git's listings (new)

- **Claim:** `git ls-files --stage -z` prints the index being committed
  exactly: one `mode SP oid SP 0 TAB path` record per stage-0 entry, each
  NUL-terminated, raw path bytes, nothing else. `ls-tree -r -z` prints a
  commit's tree, which the adapter rewrites record by record
  (`tree_record`) to the same shape. Both list paths in byte order of the
  whole path, each once (for `ls-tree -r`, tree order with `name/` for
  directories coincides with that order; tested with `a-b`, `a.c`, `a/b`,
  `a0` and non-ASCII names).
- **Trust boundary:** Git; the adapter's `tree_record` rewrite (reviewed,
  fuzz-tested in `git_output_parsers_never_panic_and_accept_only_exact_records`).
- **Consequence if false:** the hook would check entries other than those
  Git commits.
- **Evidence:** TESTED by every lifecycle suite (raw and non-UTF-8 paths,
  TABs and newlines in names); the parse PROVED both ways
  (`parse_listing_spec`), so a listing of any other shape, or out of order,
  or with a path twice, is refused. A crafted tree (`git mktree` accepts a
  repeated name, `git fsck` does not) therefore stops the hook, `verify-index`,
  `lock` and `hydrate` with an explicit message
  (`trees_listing_a_path_twice_are_refused`). The order is not trusted:
  `Sorted` is a conclusion of the parse, and lookups rely on it only after
  the parse checked it.
- **Status:** TESTED; parsing and order PROVED.

### A21 — Object replies (new)

- **Claim:** `git cat-file --batch` answers the requested object id, with
  the header `<oid> SP blob SP <size> LF`, then exactly `size` bytes and an
  LF; the adapter reads exactly those bytes.
- **Evidence:** the header must be exactly `BatchHeader` for the requested
  id with a canonical decimal size (`parse_batch_header_spec`; the size is
  unique, `batchHeader_unique`); only sizes within the record bound are
  read (`blob_read_spec`); the trailing LF is checked, also after content
  that is skipped (an oversized blob, or the rest of a blob after the first
  `ENVELOPE_PREFIX_LEN` bytes `is_record` reads), and a failed read discards
  the reader. TESTED (`git_output_parsers_never_panic_and_accept_only_exact_records`,
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
  hostile move in `git_lifecycle`, rebase and cherry-pick suites, octopus
  merges `octopus_merges_check_every_incoming_commit`). Each incoming tree
  is parsed like any tree (each path once); the adapter merges them by path
  for one lookup (`parse_listing` with `unique = false`).
- **Status:** TESTED.

### A24 — The history the incremental hook trusts

- **Claim (2026-11-02):** every regular, non-reserved entry of `HEAD` whose
  blob has the committed configuration's v3 envelope authenticates at its
  own path under that configuration (`RecordsAuthentic` in `EndToEnd.lean`).
  The claim does not mention selection: it holds whatever Git's attributes,
  committed or local, select. (The earlier, selection-dependent form,
  `HeadAuthentic`: `HEAD`'s *selected* entries authenticate, remains the
  hypothesis of the single-run
  `hook_accepts_only_authenticated_ciphertext_given_history`.)
- **Why it is needed:** the incremental pre-commit hook trusts the entries
  `HEAD` holds while the attribute files and the config are those of `HEAD`
  and `HEAD^1` (the guard): it checks only the envelope of a protected
  entry whose exact record `HEAD` and `HEAD^1` hold (*settled*, H-74: a
  commit of 10 000 files takes 0.24 s), and does not read an unprotected
  file `HEAD` holds. Theorem 1 states exactly that.
- **Why not selection (review, 2026-11-02):** the earlier invariant was about
  `HEAD`'s selected entries, and the history theorem assumed Git's `filter`
  a fixed function of the committed policy entries (`SelectionByPolicy`).
  `.git/info/attributes`, `core.attributesFile` and the system attributes
  break that: a forged record of this configuration, unselected at `p` in
  `HEAD` and `HEAD^1`, becomes selected by a local override while every
  committed attribute file is unchanged, so the guard holds and the hook
  checks only its envelope. The selection-independent invariant closes this
  for checked history: an entry staged since `HEAD` is authenticated, or is
  no record of this configuration (`NotRecord`); with the key, every
  unprotected file `HEAD` holds is authenticated if it is a record whenever
  the check does not trust `HEAD` (`AuthenticateIfRecord`: a full check,
  or the guard `false`); and the trust itself needs `HEAD` to hold the
  entry's exact record, mode included (`held_records`: a symlink staged as
  a file with the same blob was never checked as a file).
- **Proved (`EndToEnd.lean`, `ProductSecurity.lean`, PROVED (model) over the
  extracted `staged_check`, `staged_verdict`, `held_records`,
  `policy_unchanged`):**
  - *One run.* A keyed check that accepted keeps the invariant: the index's
    records authenticate given `HEAD`'s only when it trusted `HEAD`
    (incremental, guard `true`) (`hook_records_authentic`,
    `keyed_check_records_authentic`); with it, every selected entry
    authenticates (`hook_authenticated_of_records`).
  - *Bootstrap.* A keyed check that trusted nothing (`FullCheck`:
    `incremental = false`, or the guard `false`) gives the invariant and
    `AuthenticatedIndex` with **no** history hypothesis
    (`hook_full_check_authenticates`). The three modes are stated separately
    in `pre_commit_check_modes`.
  - *One transition.* If the checked index's records authenticate and the
    next `HEAD` was made from it (`CommitStep`), the next check may trust
    `HEAD`'s records under the same configuration
    (`records_authentic_of_checked_commit`); a `true` guard of the next run
    keeps the configuration (`config_unchanged_of_guard`: from the
    verified `policy_unchanged`, `CommitStep.objects` and the sorted index).
  - *Induction.* For commits `h 0 … h n`, each accepted by a keyed check
    (`KeyedCommit`) and made from the index checked before it
    (`GuardedHistoryStep`), whatever each check's mode and whatever the
    selection: every commit's records and selected entries authenticate
    (`keyed_history_authenticated_by_guard`), given only the start below.
- **Still assumed (the exact remaining obligation, for
  `keyed_history_authenticated_by_guard`):**
  1. `GuardedHistoryStep`: Git commits the index the hook checked (A22), so
     every entry of the next `HEAD` is a checked index entry and the next
     `HEAD` has the checked index's policy entries; an object id names one
     content (A11).
  2. The start of the history: the first commit's `HEAD` records must
     authenticate if its check trusted `HEAD` (incremental, guard `true`).
     A keyed `verify-index` (or `lock`, `rekey`, `doctor`) of an index that
     holds `HEAD`'s entries establishes it, as does a keyed commit whose
     guard was `false` (any change of an attribute file or the config),
     and, since 2026-11-02, **a keyed audit of the commit `HEAD` names**
     (`audited_head_starts_keyed_history`; `audited_head_keyed_history_authenticated`
     composes it with the induction): the audit keeps the same
     selection-independent invariant, authenticating every record of the
     commit's config at an unprotected path it examines. So history that
     entered without the keyed hook (`--no-verify`, cherry-pick and rebase,
     a locked checkout, another party's commits) is covered once it is
     audited with the key (pre-push, A13): a forged record committed
     without the hook at an unprotected name is refused by the keyed audit
     and the pre-push hook before anyone else relies on it
     (`local_attribute_overrides_never_admit_a_forged_record_through_checked_history`,
     `the_keyed_audit_authenticates_records_at_unprotected_paths`). What
     remains: (a) a local history that was never audited is still trusted
     by the incremental hook in that checkout (the boundary test records
     it; it cannot be pushed through the hook); (b) the audit's own start:
     the parent of the first audited commit, when it lies outside the
     range, is trusted (A13); an audit from the root trusts nothing.
  3. One key across the history (`Realizes inst prims σ` fixed); a rekey
     changes the committed configuration, so the next guard is `false` and
     the check trusts nothing.
  4. The adapter's run is as `HookEvidence`, `HookContracts` and
     `HookAnswers` say (A4): the loop and the three answers.
- The policy part of the guard is now defence in depth: the configuration
  part is what the induction needs (the invariant is per configuration);
  the attribute files part is not needed for soundness, but keeps the
  incremental hook from trusting history across a committed selection
  change.
- `HEAD` and `HEAD^1` are parsed as sorted listings, so the entry that
  holds a trusted record is the only one at its path (`Sorted.holds_oid`): a
  crafted tree cannot show one checked entry and commit another (review
  H-76).
- **Cost:** in the ordinary commit (guard `true`) nothing more is read than
  before: protected blobs and the prefixes of unprotected files staged since
  `HEAD` (`ordinary_commits_read_no_unchanged_unprotected_file`). A full
  check, and a commit that changes an attribute file or the config, reads
  the prefix of every unprotected file `HEAD` holds and the whole blob only
  of the records among them.
- **Consequence if false:** a commit made without the hook (`--no-verify`, a
  pulled commit) can hold a record that does not open at its path; the next
  incremental commit keeps it without authenticating it. `verify-index`,
  `lock`, a policy change, merge commits (for protected entries) and the
  keyed `audit` (every record it examines, selected or not, A13)
  authenticate it and refuse it.
- **Evidence:** PROVED (model) as above; TESTED
  (`newly_protected_files_are_authenticated_by_the_hook`,
  `settled_entries_are_authenticated_after_*`,
  `local_attribute_overrides_never_admit_a_forged_record_through_checked_history`,
  `local_attribute_overrides_that_unprotect_a_file_are_reversible`,
  `a_symlink_restaged_as_a_file_is_not_trusted_from_history`,
  `ordinary_commits_read_no_unchanged_unprotected_file`,
  `trees_listing_a_path_twice_are_refused`); REVIEWED.
- **Status:** narrowed: use and induction PROVED (model), with no selection
  contract; the start (2) PROVED (model) from a keyed audit of `HEAD`
  (relative to the audit's contracts and its own start, A13) or a full keyed
  check; contracts 1, 3, 4 ASSUMED (1 TESTED).

### A25 — Platform adapters (new)

- **Claim:** on each supported OS, the adapter's primitives behave as the
  shared code assumes:
  - **Unix (Linux, the BSDs, macOS; `fsat.rs`, `os_unix.rs`):** as A8.
    Peer credentials come from `SO_PEERCRED` (Linux) or `getpeereid` (the
    BSDs, macOS), and the staging lock is `flock`. A write to a pipe or
    socket whose reader left fails with EPIPE, never a SIGPIPE that ends
    the process: SIGPIPE is blocked in the writing thread, and on NetBSD
    (which signals the whole process) and macOS the descriptor is also
    marked `F_SETNOSIGPIPE`.
  - **Windows (`fsat_windows.rs`, `os_windows.rs`):**
    - Resolution: `NtCreateFile` relative to a held directory handle,
      with `FILE_OPEN_REPARSE_POINT`, resolves one component without
      following a symlink or junction. Every reparse point is refused.
    - Renames and deletions act on the file's own handle
      (`NtSetInformationFile` rename relative to the target directory
      handle; POSIX semantics where NTFS offers them) and are atomic.
    - Privacy: a protected DACL that grants only this user is private
      (as 0600/0700). It is set when the file or directory is created,
      and checked as owner plus every grant.
    - Staging lock: a second handle that asks for `FILE_ADD_FILE` and
      denies that share to others is exclusive.
    - Agent: Windows AF_UNIX sockets. The socket file sits in the private
      directory, and the peer's process token names its user.
    - Stamps: (volume, file index, size, last-write time) change on every
      write.
- **Consequence if false:** as A8 (a write outside the repository, a lost
  edit, a readable key or plaintext) and A6 (another user reaching the
  agent).
- **Evidence:**
  - TESTED: the whole v3 suite passes natively on Linux (Git 2.34 and
    2.43), FreeBSD 14.5 (Git 2.56), NetBSD 10.1 (Git 2.55), OpenBSD 7.9
    (Git 2.53; the five tests that first build a repository with Bash
    transcrypt v2 are skipped there) and Windows Server 2025 (Git for
    Windows 2.56, an ordinary user). This includes the parent-junction
    swap race, symlinked staging directories, owner-only files checked
    independently with `icacls`, hostile agent clients, SIGKILL/crash
    recovery (Unix) and stale sockets.
  - macOS runs the same Unix adapter as FreeBSD (`getpeereid`). Its suite
    runs in CI only; locally it is type-checked and linted for
    `aarch64-apple-darwin` and `x86_64-apple-darwin`.
  - Platform differences found by these runs:
    - FreeBSD's soft updates change a renamed file's ctime
      asynchronously, so stamps leave ctime out (A12).
    - NetBSD delivers SIGPIPE to the process, not the writing thread.
    - kernel32 refuses a rename relative to a directory handle; ntdll
      does it.
    - Windows children inherit every inheritable handle, so the agent
      drops the caller's standard handles.
    - `git update-index` skips a path it refuses with only a warning, so
      `IndexUpdate` reads the index back.
- **Residual:**
  - Windows: the peer check is by process id, read when the request is
    served. A peer that exits after connecting while its socket lives on
    in another process, and whose process id is reused by a process of
    this user, would pass. Reaching the socket at all needs access to
    the owner-only directory first.
  - Windows: same-user processes can read the agent's memory (no
    `PR_SET_DUMPABLE` equivalent). This is the same-user ACCEPTED RISK as
    A6.
  - Windows: last-write times may be updated lazily for a file kept open
    by its writer. A same-size in-place edit through a still-open handle
    could then be missed (A12's residual).
  - macOS: not run outside CI.
- **Next reduction:** a macOS run outside CI.
- **Status:** TESTED (Linux, FreeBSD, NetBSD, OpenBSD, Windows) + REVIEWED;
  macOS TESTED in CI only.

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
| The incremental hook counts entries as settled only while every attribute file and the config are the same in the index, `HEAD` and `HEAD^1` | `policy_unchanged_spec` (= `PolicyUnchanged`), `policy_unchanged_sound`, `is_policy_path_spec`, `is_attributes_path_spec`; spec `PolicyUnchanged.agree`, `PolicyUnchanged.holds` |
| Config authentication | `authenticate_config_spec`, `initialize_config_spec` |
| Clean never emits anything but a correct record, never double-encrypts | `seal_record_spec` |
| Smudge/verify release only authentic plaintext for this config and path | `open_record_spec`, `open_record_complete`, `opensTo_unique` |
| Agent authorization and framing | `authorize_agent_request_spec`, `decode_frame_header_encode` |
| Parsing Git's attribute answers (what is protected) | `parse_attr_record_spec` (both directions), `parse_attr_response_spec`, `parse_attr_response_complete` |
| Smudge keeps only genuine envelopes; opens only its own config | `smudge_action_spec`, `smudgeSpec_keep_envelope`, `smudgeModel_spec` |
| The pre-commit hook repairs only local changes | `repair_plan_spec`, `repairSpec_repairs_only_local`, `needs_record_spec`, `needs_record_skip`; inputs: `entry_provenance_spec`, `provenance_of_spec`, `next_move_source_spec`; composed in `hook_provenance`, `hook_skips_only_unrepairable`, `hook_repairs_only_local_changes` |
| Git listings are parsed exactly; each entry's fields | `parse_listing_spec` (both directions), `listing_fields_spec` |
| Selection checked against the listing's own paths; selectability | `parse_listing_attrs_spec` (both directions), `first_unselectable_spec` |
| Keyless move check | `blob_elsewhere_spec` |
| Stored-key decision | `stored_key_state_spec`, `storedKeySpec_unlocked`, `stored_key_authenticates_current_config` |
| Which key a configuration is used with: the stored file's own key bytes, only for the config they authenticate (relative to `KeyScheduleRealizes`) | `authenticate_key_spec`, `unlock_stored_key_spec`, `stored_key_binds_file_operations` |
| `cat-file --batch` reply framing | `parse_batch_header_spec`, `batchHeader_unique`, `blob_read_spec` |
| Each entry's final check and its acceptance, decided by the core | `staged_check_spec`, `held_records_spec`, `reads_blob_spec`, `staged_verdict_ok`; composed in `hook_entry_checked` |
| End to end: the hook accepts only authenticated ciphertext at the selected paths | `hook_accepts_only_authenticated_ciphertext` (with `index_verdict_accepts`, `hook_entry_checked`) |
| The A24 history: every keyed commit's records authenticate, whatever selects paths | `hook_records_authentic`, `keyed_check_records_authentic`, `records_authentic_of_checked_commit`, `config_unchanged_of_guard`, `keyed_history_authenticated_by_guard` (model) |
| Index record parsing | `parse_index_entry_spec` |
| Git filter-protocol packet lengths | `decode_pkt_len_spec` |
| Object ids passed to Git are plain hex names, taken from the right bytes | `is_object_id_spec`, `objectId_plain`, `indexRecord_oid` |
| Keyless envelope check | `record_envelope_ok_spec`, `opensTo_envelopeOk`, `record_envelope_prefix_ok_record` |
| Clean and locked-filter behavior (models of adapter compositions) | `cleanModel_spec`, `cleanModel_genuine`, `cleanModel_idempotent`, `lockedFilterModel_spec` |
| Hydrate/lock never lose data; verify-index soundness | `hydrate_action_spec`, `lock_action_spec`, `hydratePlan_spec`, `lockEntry_spec`, `verifyPlan_spec` |

## Adapter call-site table (A4)

Each effect in `rust/crates/transcrypt-rs/src/{main,git,worktree,setup,audit,session,fsat,lib}.rs` and the
verified decision that gates it:

| Adapter action | Gate (verified core function) | Inputs passed | Acts only on |
| --- | --- | --- | --- |
| `clean` filter output (unlocked) | `Key::clean` → `ValidatedKey::clean` (stored key) or agent `Encrypt` (private): `open_record` (authentic record ⇒ returned unchanged) else `seal_record` | config bytes from `.transcrypt/config`; Git `%f` bytes; stdin | `Ok` (else Git aborts) |
| `smudge` filter output | `smudge_action` (no envelope ⇒ refuse; other config or locked ⇒ keep the record; own config ⇒ open), then `open_record`; private mode: `umask_is_private` chooses plaintext or the authenticated record | same config; `%f`; blob from stdin | `Ok` |
| `clean` while locked | `record_envelope_ok` against `config_id(config)` | stdin | `true` ⇒ input unchanged; else refuse |
| Key loading | `unlock_stored_key` (layout, `stored_key_state`, `authenticate_key` on the file's key bytes; returns the primitives and the config, held in a `ValidatedKey`), or agent `Ping` | stored key file (config ‖ 64-byte key); current config | `Ok`; `unlock` replaces a `Damaged` file |
| Protected-file selection | `parse_attr_response` over the whole answer (one record per requested path, in order, nothing else); `is_reserved_path` | raw paths sent to `check-attr -z --stdin filter` (`--cached`, worktree, or a commit's temporary index) | `protected = true` |
| Pre-commit re-encryption (`seal_staged`) | `entry_provenance` over the index, `HEAD` and incoming listings, then `needs_record`; only then the blob's `RecordClass` (`open_record` at its path, `parse_file_header`, `open_record` at each `next_move_source` path), and `repair_plan` on the two; then `ValidatedKey::clean`/`seal_record` at the new path | staged blobs by oid; `HEAD` and incoming listings (`parse_listing`); sequencing state | `Seal` or `Rebind(j)` only |
| Agent framing | `encode_frame_header` / `decode_frame_header`, `encode_be_u32` / `decode_be_u32` | opcode, config, lengths | proved roundtrip |
| Git filter-process framing | `decode_pkt_len` for every packet; then the same conversion as the per-file filters | 4-byte pkt-line headers from Git; `command=`/`pathname=` values | `Ok` (else the process ends and Git fails) |
| Agent dispatch | `authorize_agent_request` before the body is read; peer UID check | opcode, supplied config, startup config, path, length | `Ok(op)` from a same-UID peer |
| Agent startup | `authenticate_key` (`ValidatedKey::authenticate`) | config bytes, piped key | `Ok`; the agent holds only that `ValidatedKey` |
| `unlock` / `init` | `authenticate_key` / `initialize_config` then `authenticate_key` (`ValidatedKey::unlock` / `initialize`) | config bytes / fresh salt | `Ok`, before any persistent effect |
| Index and tree listings | `parse_listing` (whole listing: records, object ids), then `listing_fields` per entry | `ls-files --stage -z`, or `ls-tree -r -z` records rewritten to that shape (path copied verbatim) | `true` (else refuse) |
| Object reads | `is_object_id`, then `parse_batch_header` and `blob_read` | oid from the parsed snapshot | `true`; one `cat-file --batch` per process; header exactly `<oid> blob <size>` (canonical decimal), `Read` only within 16 MiB, trailing LF checked |
| `verify-index` and the hook's check | `parse_listing_attrs`, `first_unselectable`, `held_records`, `policy_unchanged`, then one call of `index_verdict`: for every entry `staged_check`, `reads_blob` and `staged_verdict`, which asks `is_record` (`record_envelope_prefix_ok`), `opens` (`open_record` via `Key::open`) and `elsewhere` (`blob_elsewhere`) only as needed | snapshot listing; blobs by oid | `Ok` (a failed read or answer is `None` and refused by the core) |
| `hydrate` publish | agent `Decrypt`, then `hydrate_action`, all entries before any write; stamp equality | blob by snapshot oid; worktree bytes and stamp via held dirfd | `Ok(Publish)` for all; `Keep` untouched |
| `lock` flush | agent `Encrypt` (reseal), then `lock_action`; stamp equality | worktree bytes and stamp, blob by oid, reseal output | `Ok(Flush)`; `Keep` untouched |
| Re-index after hydrate/lock | none (bookkeeping); listing compared with the verified snapshot afterwards | verified protected paths, raw, via `update-index -z --stdin` | listing unchanged |
| `audit` / `pre-push` | `parse_index_entry`, `is_object_id`, `parse_config`, selection with the commit's attribute files, `record_envelope_ok`, no blob moved from a deleted path, `open_record` when the key authenticates that config | `ls-tree`/`diff-tree` per commit; blobs by oid | every protected entry `true`/`Ok` |
| `rekey` staging | `open_record` of each staged record, equality with the worktree, then `seal_record` under the new config (`ValidatedKey::encrypt` of the new config's key); `initialize_config` for the new config; config written by `write_repository_file` (dirfd, no symlinks) | staged blobs by oid, worktree bytes, fresh salt | all `Ok`, before any index or credential change |
| `protect` / `unprotect` / `init` / `migrate` | selection before and after the `.gitattributes` edit (written by `write_repository_file`); `seal_staged` with the newly selected paths; `open_record` before staging plaintext on `unprotect`; reserved metadata refused | attribute files; staged blobs | all `Ok`, or the edit is reverted |
| `uninstall` | `lock` (above), then `record_envelope_ok` for every protected worktree file | worktree bytes | all `true` before removing filters |
| `doctor` | none (read-only checks of Git config, attributes, hooks, `check_index`) | — | reports only |
| Merge driver | agent `Decrypt` (`open_record`) of ours and theirs at `%P` (base: empty if it does not open), `git merge-file`, agent `Encrypt` (`ValidatedKey::clean`) of the result | Git's `%O %A %B` files, `%P` path | both `Ok` (else `ours` is left unchanged and Git records a conflict) |
| Diff driver | `record_envelope_ok`, then agent `Decrypt` (`open_record`) of each record side at its own path | Git's external diff arguments | `Ok` (else Git stops the diff) |
| `hydrate` during a merge | unmerged paths: `record_envelope_ok`, agent `Decrypt`, `hydrate_action`; effective filter checked for every protected path | worktree bytes | `Ok(Publish)` |

The Lean lifecycle models (`Lifecycle.lean`) reproduce the hydrate, lock and
verify loops in this order. Review rule: a new effect in the adapter must
appear in this table with its gate, or it is a regression.
