# Transcrypt v3: what the proofs guarantee

Transcrypt v3 protects the files you select in public Git history using
encryption that is authenticated and bound to the repository's configuration
and to each file's exact path. The Lean proofs establish three things about
the verified Rust protocol:

- how it authenticates records;
- that a decrypted file is released only after its record authenticates;
- that the pre-commit hook checks the staged state before publication, and
  that its repair step never launders content from another commit.

The proofs also show that a history built from keyed commits, each checked
properly, keeps these properties from commit to commit. Every guarantee rests
on cryptographic, Git and operating-system contracts. Each card below names
them, so a reader can see exactly what is proved and what is trusted.

All four public theorems are in one file,
[`ProductSecurity.lean`](../../proofs/aeneas/v3/V3Wire/Verification/ProductSecurity.lean).
The theorems they build on are listed in the
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

## A. Authenticated publication

- **Claim:** When a keyed publication check accepts, every selected file in
  the index it checked authenticates under the repository's committed
  configuration at its exact Git path.
- **Why it matters:** It excludes publishing plaintext, a forged record, a
  record sealed for another path (a file swapped or renamed without the
  key), and a record of another configuration.
- **Lean theorems:**
  - `keyed_publication_authenticates` (full or incremental).
  - `hook_full_check_authenticates`: a full check needs no trusted history.
  - `pre_commit_check_modes`: the three modes.
- **Source connection:**
  - The decision `hookPlan` is composed from the extracted `entry_check`,
    `record_envelope_ok` and `open_record`, together with the listing,
    attribute and selection parsers (`parse_listing`, `parse_listing_attrs`,
    `first_unselectable`, `held_entries`).
  - Whether an entry is settled comes from the extracted `policy_unchanged`
    and `held_entries`; the guard has its own proof (see "Checked history"
    below).
  - Production Rust: `lifecycle.rs` `check_staged` and the core's
    `lib.rs`.
- **Assumptions:**
  - A4 (the adapter feeds Git's real snapshots to these functions and obeys
    their answers);
  - A16 and A19 (Git's attribute selection);
  - A20 and A21 (listings and object reads);
  - A5, A9 and A10 (the primitives realize `Realizes`);
  - for an incremental check, also A24 (below).
- **Limitations:**
  - It is about the index the hook checked. That this index is what Git
    commits is A22.
  - Commits made without the keyed hook are covered only by the keyed
    `audit` at push time (A13). This includes `--no-verify`, a locked
    checkout, a rebase, and another party's commits.
- **Status:**
  - The decision functions: source-derived proof.
  - The composition (`HookEvidence`, `hookPlan`): model proof.
  - The adapter's sequencing: tested and reviewed.

## B. Authenticated recovery

- **Claim:** Checkout writes decrypted plaintext only if the record
  authenticates under the expected configuration, key and path. When
  authentication fails, the plaintext is never released.
- **Why it matters:** A tampered, truncated, reordered or misplaced record
  can never reach the worktree as plaintext. An attacker cannot make a
  failed authentication look like a decryption.
- **Lean theorems:**
  - `checkout_releases_only_authenticated_plaintext`. Every output differs
    from the record only if it is exactly the plaintext the record
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
- **Lean theorem:** `repair_never_launders`. It proves four things:
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
  it authenticates. Every file sealed or opened with it is bound to that
  configuration and to the exact path.
- **Why it matters:** A stale key, or a key for another repository or for
  the configuration before a rekey, is refused as "locked" or "stale". It is
  never used to produce or accept records.
- **Lean theorem:** `stored_key_binds_file_operations`. It composes
  `stored_key_authenticates_current_config`, `open_record_spec`,
  `seal_record_spec` and `seal_opens`.
- **Source connection:** The extracted `stored_key_state` and
  `authenticate_config`, then `seal_record` and `open_record`. Production
  Rust: `credential.rs`.
- **Assumptions:**
  - A17 (the key file is read as stored and kept local);
  - A5, A9 and A10.
- **Limitations:**
  - The theorem does not prove that Argon2id resists offline guessing.
  - It does not prove that a persisted key came from a particular `init`
    or `unlock`.
  - It does not prove anything about how the key is protected at rest.
- **Status:**
  - The decision: source-derived proof.
  - The file I/O: tested and reviewed.

## Checked history (A24)

The incremental hook re-checks only the envelope of a "settled" entry, one
that is unchanged since `HEAD` and `HEAD^1`. This is what lets a commit
avoid decrypting thousands of unchanged files. In return, it trusts that
`HEAD` was itself authenticated. Three results are proved:

- **Bootstrap (`hook_full_check_authenticates`):** a full keyed check
  authenticates the index with no history hypothesis.
- **Transition (`head_authentic_of_checked_commit`):** suppose an
  authenticated index is committed (`CommitStep`), and neither the selection
  nor the configuration changed (`PolicyUnchanged`). Then the next check may
  trust `HEAD`.
- **Induction (`keyed_history_stays_authenticated`):** a sequence of keyed
  commits stays authenticated if two conditions hold:
  - it starts with a full check;
  - every incremental check follows a commit whose policy was unchanged.

The guard that decides whether entries may be settled is source-derived.
`policy_unchanged` compares the committed attribute files and
`.transcrypt/config` across the index, `HEAD` and `HEAD^1`, and
`policy_unchanged_sound` proves that when it returns true, the three
snapshots agree exactly on those files. A policy change therefore forces a
full check.

**Remaining obligations** (all stated in [A24](V3-ASSUMPTIONS.md)):

- **Commit flow:** Git commits the checked index, and object ids are
  unique (A22, A11).
- **Selection:** unchanged committed attribute files mean an unchanged
  selection (A19). Local attribute sources are excluded:
  `.git/info/attributes` and `core.attributesFile`.
- **Start of each run of keyed commits:** commits made without the keyed
  hook must be checked by the keyed `audit` before they are trusted (A13).
- **Connecting the guard to the model:** the guard's result is not yet a
  field of the hook model's `settled` flag, so the guard and the transition
  theorem are joined in prose.

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
