# Transcrypt v3: what the proofs guarantee

## The product guarantee

Suppose you unlocked a checkout, so that the verified stored-key check
accepted the key file for the repository's current configuration, and you
commit through the keyed pre-commit hook, starting from a commit the keyed
audit accepted with the same key (or from a commit whose check
authenticated everything). Then, as long as Git, the adapter code around
the verified core and the cryptographic primitives meet their stated
contracts:

- every commit you make stores each file its committed `.gitattributes`
  select as a record that authenticates under that configuration at exactly
  that file's path, and every record of that configuration anywhere in the
  index authenticates at its own path;
- checkout releases plaintext only after the record authenticates at its
  exact path under that configuration, never after a failure, and every
  genuine record opens;
- the hook's repair step encrypts only plaintext you staged (or explicitly
  `protect`ed) and re-encrypts only your own renames, never content imported
  from another commit;
- all of this uses only the key whose file names this configuration,
  authenticates it and holds its own check value for it.

Nothing here is a confidentiality theorem, and Git and the operating system
are not verified.

## The theorem

That paragraph is one Lean theorem, `transcrypt_product_assurance`, in
[`ProductAssurance.lean`](../../proofs/aeneas/v3/V3Wire/Verification/ProductAssurance.lean).
It composes the product theorems of
[`ProductSecurity.lean`](../../proofs/aeneas/v3/V3Wire/Verification/ProductSecurity.lean)
and [`Audit.lean`](../../proofs/aeneas/v3/V3Wire/Verification/Audit.lean).
The parts must agree. One crypto context, the output of the verified
`unlock_stored_key`, is used by every publication check, audit, checkout and
repair in the statement. Each commit's configuration is the one the key
validated, and the history starts exactly where the audit theorem leaves
off.

| Part of the statement | Predicate | Card below |
| --- | --- | --- |
| Hypothesis: the stored key unlocked | `StoredKeyUnlocked` (`unlock_stored_key` returned `Ok`; the id is the configuration's digest, A5) and `KeyScheduleRealizes` (A5, A17) | D |
| Hypothesis: each commit is a keyed publication with that key and configuration | `ValidCheckedPublication` (wraps `KeyedCommit`: `HookContracts`, `ConfigCommitted`, `KeyedCheckAccepted` with `HookAnswers`) | A |
| Hypothesis: Git commits the checked index | `GuardedHistoryStep` (A22, A11) | Checked history |
| Hypothesis: how the history starts | `HistoryStart`: a check that trusted nothing, or a `KeyedAuditRange` ending at `HEAD` (`KeyedAudit` with `AuditContracts` and `AuditAnswers`; `AuditStep`; the parent of its first commit, A13) | Checked history |
| Conclusion: key use | `ValidatedCryptoContext` (from `stored_key_binds_file_operations`) | D |
| Conclusion: every checked state is authenticated | `AuthenticatedRepositoryState` (`RecordsAuthentic` and `AuthenticatedIndex`) | A, Checked history |
| Conclusion: recovery | `AuthenticatedRecovery` (`CheckoutOutcome` for every smudge run; genuine records open) | B |
| Conclusion: repair | `NoLaunderingRepair` for every repair decided with that key (`RepairContracts`) | C |

Within those contracts, the theorem rules out:

- publishing plaintext, a forged record, or a record sealed for another
  path or another configuration;
- releasing unauthenticated plaintext;
- turning imported content into an accepted record;
- using a stale key, a key for another configuration, or a damaged key.

It uses only Lean's standard axioms (`check-v3-axioms.sh`). The theorems it
builds on are listed in the
[proof ledger](../../proofs/aeneas/v3/PROOF-STATUS.md). The full argument is
in [V3-SECURITY-ARGUMENT.md](V3-SECURITY-ARGUMENT.md), and every assumption
is defined in [V3-ASSUMPTIONS.md](V3-ASSUMPTIONS.md).

**How to read the status labels.**
- *Source-derived proof:* the theorem is about the Lean that Aeneas extracts
  from the production Rust core.
- *Model proof:* the theorem is about a handwritten Lean model of how the
  adapter uses the core.
- *Tested* and *reviewed* are evidence, not proof.
- *Assumed:* the property is trusted.

A document is not evidence. Only the theorems and tests it names are.

## Keyed and keyless verification

- **Keyed check:** runs when the key is available. It decrypts each record
  and accepts it only if it authenticates under this configuration at its
  exact path. This is the only check that stops forged or misplaced records.
- **Keyless check:** used in a locked checkout, a CI job without the
  passphrase, or a server hook. It looks only at the envelope: the v3
  header and this configuration's id. That stops plaintext from being
  published by accident, but a forged envelope with the right header passes
  (A14).

The hook and `verify-index` say which kind of check they ran. Without the
key they print "checked staged record envelopes only, which does not
authenticate them". `pre_commit_check_modes` states the full keyed,
incremental keyed and keyless results separately.

The audit (`transcrypt-rs audit`, the pre-push hook, a server hook) makes
the same distinction. **Keyed**, it authenticates every selected record at
its path and every record of the commit's configuration it examines at an
unprotected path (`keyed_audit_authenticates_commit`). **Keyless**, it
checks that every selected file has the envelope and is not a record moved
from a deleted path, and refuses a record moved to an unprotected name; it
authenticates nothing, and says "envelopes only: unlock to authenticate
them and any record at an unprotected path"
(`keyless_audit_checks_envelopes`).

## A. Authenticated publication

- **Claim:** When a keyed publication check accepts, every selected file in
  the index it checked authenticates under the repository's committed
  configuration at its exact Git path.
- **Why it matters:** It excludes publishing plaintext, a forged record, a
  record sealed for another path (a file swapped or renamed without the
  key), and a record of another configuration.
- **Lean theorems:**
  - `keyed_publication_authenticates` (full or incremental).
  - `keyed_check_records_authentic`: with the key, every record of this
    configuration in the index authenticates at its own path, whatever
    selects paths (see "Checked history" below).
  - `hook_full_check_authenticates`: a full check needs no trusted history.
  - `pre_commit_check_modes`: the three modes.
- **Source connection:**
  - Each index entry's check is decided by the extracted `staged_check`
    (which check: authenticate, envelope, envelope and not moved, no
    record, authenticate if a record, or nothing) and accepted by the
    extracted `staged_verdict` (with `entry_check`, `parse_file_header`,
    `record_envelope_ok`). The Lean loop `hookPlan` only sequences these two
    calls; it reimplements nothing.
  - The verdict asks the adapter three questions (`StagedEvidence`), each
    only when its check needs it: is the blob a record of this
    configuration (`record_envelope_prefix_ok`), does it open at its path
    (`open_record`), and is it another path's blob (`blob_elsewhere`).
  - The inputs come from the listing, attribute and selection parsers
    (`parse_listing`, `parse_listing_attrs`, `first_unselectable`), exact
    record membership in `HEAD` and `HEAD^1` (`held_records`) and the guard
    (`policy_unchanged`).
  - Production Rust: `lifecycle.rs` `check_staged` (and its `EntryEvidence`)
    and the core's `lib.rs`.
- **Assumptions:**
  - A4 (the adapter feeds Git's real snapshots to these functions, runs the
    loop over every entry, answers the three questions truthfully about the
    entry's own blob and path, and obeys the verdict: `HookAnswers`);
  - A16 and A19 (Git's attribute selection);
  - A20 and A21 (listings and object reads);
  - A5, A9 and A10 (the primitives realize `Realizes`);
  - for an incremental check, also A24 (below).
- **Limitations:**
  - It is about the index the hook checked. That this index is what Git
    commits is A22.
  - Commits made without the keyed hook are covered by the keyed `audit`
    at push time (A13; see "Checked history"). This includes
    `--no-verify`, a locked checkout, a rebase, and another party's
    commits.
- **Status:**
  - The decision functions, the per-entry check and its acceptance:
    source-derived proof.
  - The composition (`HookEvidence`, `hookPlan`): model proof (a loop over
    the extracted functions).
  - The adapter's loop and its three answers: tested and reviewed.

## B. Authenticated recovery

- **Claim:** Checkout writes decrypted plaintext only if the record
  authenticates under the expected configuration, key and path. When
  authentication fails, the plaintext is never released.
- **Why it matters:** A tampered, truncated, reordered or misplaced record
  can never reach the worktree as plaintext. An attacker cannot make a
  failed authentication look like a decryption.
- **Lean theorems:**
  - `checkout_releases_only_authenticated_plaintext` (`CheckoutOutcome`).
    Every output differs from the record only if it is exactly the plaintext the record
    authenticates to. An output equal to the record is the record kept
    as-is, which has a v3 header. If the decision was to open and nothing
    authenticates, the result is `none`.
  - `checkout_opens_genuine_records`: a genuine record of this
    configuration always opens.
- **Source connection:** The extracted `smudge_action` and `open_record`,
  through `smudgeModel`. Production Rust: `filter.rs` (smudge) and the
  core's `open_record`.
- **Assumptions:**
  - A5, A9 and A10 (`Realizes`);
  - A4 (the filter writes what the core returned);
  - A7 (Git delivers the record and path it filters).
- **Limitations:**
  - A successful smudge does not always produce plaintext. A locked
    checkout, a checkout of another configuration, and private mode
    deliberately keep the ciphertext.
  - Determinism means equal plaintexts at one path give equal records, so
    equality is visible.
  - A record from an earlier commit at the same path still authenticates
    (replay).
- **Status:**
  - The decision and decryption: source-derived proof.
  - `smudgeModel`: model proof.
  - Tampering: tested exhaustively.

## C. No laundering of foreign history

- **Claim:** The pre-commit repair step does two things: it encrypts a file
  the user staged as plaintext, and it re-encrypts a record the user renamed
  for its new path. It never turns content imported from another commit
  into an accepted protected record.
- **Why it matters:** A hostile commit cannot get a forged or misplaced
  record "repaired" into a genuine one by the next person who commits.
- **Lean theorem:** `repair_never_launders`. Its conclusion,
  `NoLaunderingRepair`, has four parts:
  - A seal is only of the user's own change or of plaintext that `protect`
    forced, and never of a record with a v3 header.
  - A rebind is only of the user's change, and its record authenticates at
    the path of the `HEAD` entry it was moved from.
  - Content held by `HEAD` or by the commits being brought in is never
    rebound. It is sealed only when `protect` explicitly forced it.
  - The user's change is never skipped.
- **Source connection:** The extracted `entry_provenance`, `needs_record`
  and `repair_plan` (with the `Provenance`, `RecordClass` and `RepairPlan`
  types) and `next_move_source`. Production Rust: `lifecycle.rs`
  `seal_snapshot`.
- **Assumptions:**
  - A4 (`RecordEvidence`: the adapter classifies each blob honestly);
  - A23 (the sequencing state names the incoming commits);
  - A20 and A21.
- **Limitations:** `protect` is an explicit request to encrypt plaintext
  that is already committed, so it is the one way to seal content that came
  from history. A forced seal applies only to content without a v3 header;
  it never rebinds a record and never accepts one without authentication.
- **Status:**
  - The decisions and their inputs: source-derived proof.
  - The repair loop: model proof.
  - Hostile merges, cherry-picks and moves: tested.

## D. Configuration-bound key use

- **Claim:** A persisted derived key is accepted only for the configuration
  it authenticates, and only with its own check value for that
  configuration; the primitives used are built from exactly that file's
  key bytes. Every file sealed or opened with them is bound to that
  configuration and to the exact path.
- **Why it matters:** A stale key, or a key for another repository or for
  the configuration before a rekey, is refused as "locked" or "stale". It is
  never used to produce or accept records, and no other key can be paired
  with the configuration afterwards. A damaged key file is refused, not
  used to seal records that teammates could not open: the configuration tag
  depends on only the S2V half of the AES-SIV key, the check value (a
  sealed nonempty constant) on both halves.
- **Lean theorem:** `stored_key_binds_file_operations`. Its premise is the
  output of the verified `unlock_stored_key` (the primitives and the
  configuration the adapter keeps), not an arbitrary primitive instance.
  Its conclusion, `ValidatedCryptoContext`, includes that the primitives
  realize the suite of the file's own key bytes. This is how the top-level
  theorem gets its one crypto context. It concludes, besides the bindings, that the file's check value is the
  suite's `keyCheckValue` for the configuration. It composes
  `unlock_stored_key_spec` (with `authenticate_key_spec`,
  `key_check_opens_spec` and `stored_key_state_spec`), `open_record_spec`,
  `seal_record_spec` and `seal_opens`; `seal_key_check_spec` and
  `key_check_round_trip` cover the check value `store` writes.
- **Source connection:** The extracted `unlock_stored_key`,
  `authenticate_key`, `key_check_opens`, `seal_key_check`,
  `stored_key_state` and `authenticate_config`, then `seal_record` and
  `open_record`. Production Rust: `ValidatedKey` in `lib.rs` (private
  fields; built only from `authenticate_key` and `unlock_stored_key`;
  `to_stored` writes the file through `seal_key_check`) and
  `credential.rs`.
- **Assumptions:**
  - `KeyScheduleRealizes` (A5, A17): `Keyed::from_key(k)` realizes the
    suite of exactly the bytes `k`;
  - A17 (the key file is read as stored and kept local);
  - A9 and A10 (A10 includes that a key differing in either half gives a
    different check value, so that damage is detected).
- **Limitations:**
  - The theorem does not prove that Argon2id resists offline guessing.
  - It does not prove that a persisted key came from a particular `init`
    or `unlock`, or from a passphrase at all.
  - It does not prove anything about how the key is protected at rest.
  - That the check value detects a damaged key is AES-SIV's property, not
    proved; it is tested for every single-bit change of the key and the
    check value (A17).
  - A key file of the earlier layout (config and key, 119 bytes) is
    refused as damaged until `unlock` rewrites it.
- **Status:**
  - Key selection, pairing and the check value: source-derived proof,
    relative to the key schedule contract.
  - The interface: structural (`ValidatedKey`), with a source scan test.
  - The file I/O and the key schedule: tested and reviewed.

## Checked history (A24)

The incremental hook trusts what `HEAD` holds while the committed
attribute files and `.transcrypt/config` are those of `HEAD` and `HEAD^1`
(the guard): it re-checks only the envelope of a "settled" protected entry,
one whose exact record `HEAD` and `HEAD^1` hold, and does not read an
unprotected file `HEAD` holds. This is what lets a commit avoid decrypting
thousands of unchanged files. In return, it trusts an invariant of `HEAD`
that does not depend on selection: every record of this configuration at a
regular, non-reserved path authenticates at that path (`RecordsAuthentic`).
Because the invariant does not mention selection, a local attribute source
(`.git/info/attributes`, `core.attributesFile`) that starts selecting a path
cannot turn a forged record of checked history into an accepted protected
file. Four results are proved:

- **One run (`keyed_check_records_authentic`, `hook_records_authentic`):** a
  keyed check that accepted keeps the invariant, trusting `HEAD`'s records
  only when it was incremental with the guard true. An entry staged since
  `HEAD` is authenticated or is no record of this configuration; with the
  key, an unprotected file `HEAD` holds is authenticated if it is a record
  whenever the check does not trust `HEAD`. Every selected entry then
  authenticates (`hook_authenticated_of_records`).
- **Bootstrap (`hook_full_check_authenticates`):** a keyed check that trusts
  nothing (not incremental, or the guard false) establishes the invariant
  and authenticates the index with no history hypothesis.
- **Transition (`records_authentic_of_checked_commit`,
  `config_unchanged_of_guard`):** the checked index's records are the next
  `HEAD`'s (`CommitStep`), and a true guard keeps the configuration.
- **Induction (`keyed_history_authenticated_by_guard`):** a sequence of keyed
  commits keeps the invariant and authenticates every selected path, with no
  hypothesis about the policy or about how Git selects paths on any step.
- **The keyed audit (`keyed_audit_authenticates_commit`, `Audit.lean`):**
  for history the hook never saw, a keyed audit of one commit keeps the same
  invariant. It examines what the commit changes against its first parent
  (its whole tree for a root commit, a config change or an attribute
  change), and each examined entry is checked by the extracted
  `audit_check` and `staged_verdict`, the hook's vocabulary: a selected
  entry authenticates; an unprotected file the parent holds exactly is
  trusted from the parent while the config is unchanged; any other
  unprotected file, if it is a record of the commit's config (a prefix
  read), must authenticate at its path. If it accepted, the commit's records
  authenticate given its parent's (nothing is needed for a root commit or a
  config change), and so does every path the commit's attributes select.
- **Start (`audited_head_starts_keyed_history`,
  `audited_head_keyed_history_authenticated`):** a keyed audit of the
  commit `HEAD` names establishes the start of the induction, so an audited
  `HEAD` followed by keyed commits keeps every commit authenticated.
  `keyed_audit_chain_authenticated` is the induction over a chain of
  audits, each commit's parent the one before.

The guard is source-derived: `policy_unchanged` compares the committed
attribute files and `.transcrypt/config` across the index, `HEAD` and
`HEAD^1`, and `policy_unchanged_sound` proves that when it returns true the
three snapshots agree exactly on those files (`hook_policy_guard`). Its
configuration part is what the induction uses; its attribute part is
defence in depth.

**Remaining obligations** (all stated in [A24](V3-ASSUMPTIONS.md)):

- **Commit flow:** Git commits the checked index, so the next `HEAD` has
  its entries and its policy entries (`GuardedHistoryStep`), and object ids
  are unique (A22, A11).
- **Start of each run of keyed commits:** the first commit's `HEAD` records
  must authenticate if its check trusted `HEAD`. A keyed audit of `HEAD`
  establishes this (proved, relative to the audit's contracts), as do a
  keyed `verify-index` of a checkout whose index holds `HEAD`'s entries and
  a keyed commit that changes an attribute file or the config. The audit's
  own start is the parent of the first commit it audits: an audit from the
  root trusts nothing, and the pre-push range trusts what the remote
  already has (A13). A forged record committed without the keyed hook at an
  unprotected name is refused by the keyed audit and the pre-push hook; a
  local history that was never audited is still trusted by the incremental
  hook in that checkout, even once a local override selects the record (a
  tested boundary: it cannot be pushed through the pre-push hook).
- **The audit's adapter** reports what Git lists: every entry it does not
  examine is the parent's exactly, and its selection of such an entry is
  the parent's (`AuditContracts`, `AuditSelectionAgrees`; A19, A20). Its
  per-run cache of checked records is tested, not modelled.
- **The adapter** answers the verdict's three questions truthfully (A4).

## What remains trusted

These are the hypotheses of `transcrypt_product_assurance` and the
boundaries it does not cross. Each is defined in
[V3-ASSUMPTIONS.md](V3-ASSUMPTIONS.md).

- **The key schedule** (A5, A17): `Keyed::from_key(k)` realizes the suite of
  exactly the bytes `k`, and `config_id` is its digest. This is tested, not
  proved.
- **The primitives and their security** (A9, A10): RustCrypto computes
  AES-SIV, Argon2id and SHA-256 correctly, and they are secure. A10 also
  covers the check value detecting a damaged key.
- **The adapter around the core** (A4): it runs the loops of the hook and
  the audit over every entry and answers truthfully (`HookAnswers`,
  `AuditAnswers`, `RecordEvidence`), and the filters write what the core
  returned. The loops, `smudgeModel` and the audit's record cache are
  models or tests, not extracted code.
- **Git** (A11, A19–A21, A23): its listings, attribute answers, object reads
  and sequencing state are what the contracts say.
- **Git commits the checked index** (A22), so each step is a
  `GuardedHistoryStep`.
- **The start of the audited range** (A13): the parent of the first audited
  commit is trusted when it lies outside the range, so the pre-push range
  trusts what the remote already has. An audit from the root, or from a
  configuration change, trusts nothing.
- **An unaudited local checkout** (A24, open): the theorem needs a
  `HistoryStart`. A local history that was never audited is still trusted
  by the incremental hook in that checkout. This is tested: such a history
  cannot pass the pre-push hook.
- **Translation and the kernel** (A3): Charon/Aeneas and Lean are sound.
- **Private mode** (A6): the theorem's key is the stored key. The agent of
  `--private` calls the same verified functions, and this is tested, not
  part of the statement.

## What is not claimed

- **No cryptographic security:** there is no confidentiality or
  computational security theorem. AES-SIV, Argon2id and SHA-256 are assumed
  secure (A10), and offline password guessing is not addressed.
- **Equality and replay remain:** deterministic encryption shows when two
  plaintexts at the same path are equal, and an old record at the same path
  can be replayed.
- **Git and the OS are not verified:** they are trusted through the named
  contracts (A7, A8, A11, A19–A23).
- **No local secrecy:** an unlocked checkout holds plaintext by design.
  Anyone with your account or unrestricted local Git access can stage
  plaintext on purpose.
