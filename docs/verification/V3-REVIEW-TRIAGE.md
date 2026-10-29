# Independent review disposition against the v3 product charter

**Review received:** 2026-10-25. **Reviewed source:** commit `861975ad`
(the supplied `2026-10-25T132743` archive); the report did **not** execute
the Rust v3 binary. This is a **triage and test plan**, not a claim that the
findings are fixed in HEAD. Always recheck current code, tests and history
before assigning a current vulnerability status.

**Original independent report:**
[reviews/2026-10-25-independent-source-assessment.md]
(reviews/2026-10-25-independent-source-assessment.md). This source-level
assessment is distinct from an independent cryptographic library audit and
from the project's older internal review. Preserve its actual findings,
reproduction levels and caveats rather than rewriting them to fit the vision.

**Normative lens:** [V3-PRODUCT-CHARTER](V3-PRODUCT-CHARTER.md). The principal
promise is authenticated encrypted public Git content with transparent,
recoverable local Git use. Local-at-rest secrecy against other workstation
users is *not* a default requirement. Real adapter bugs still count.

## Disposition table

| Finding | Evidence reported | Product classification | Required next action | Status for this review snapshot |
| --- | --- | --- | --- | --- |
| **F-01**: Bash v2 `U2FsdGVk` magic-prefix plaintext bypass | Reproduced using the actual Bash clean and pre-commit code | **Real legacy public-history confidentiality flaw**, high impact for v2 users; not a reason to add legacy CBC to proved v3 | Fix the Bash pass-through assumption for maintained v2 users or provide prominent warning and explicit incident-response/migration guidance; test with the actual filter and hook; audit exposed history. Keep v2 outside the v3 formalized core | **Fixed** in commit `c3c2bc8`: reproduced on the unmodified script first; ciphertext is now accepted only if it decrypts under the key and embeds the per-path salt; new bats regressions for clean and pre-commit (218/218 pass). Residual: v2 is unauthenticated; old installs need `transcrypt --upgrade`; history before the fix needs an audit |
| **F-02**: `rekey` writes predictable `.transcrypt/config.rekey` following a symlink | Source analysis + independent POSIX write/rename reproduction; Rust command was **not** executed | **Must fix v3**: attacker-controlled repository state can corrupt a file outside the repo; also threatens config integrity and recovery | Reproduce with compiled `transcrypt-rs rekey` in a disposable clone and an outside sentinel; use the existing checked fd-relative, no-follow, exclusive temp/atomic replacement infrastructure; regression for no external writes, correct config and recoverability | **Fixed**: reproduced with the compiled binary on `d8436c6` (the write followed the committed symlink and left `.transcrypt/config` a symlink). All repository-file writes now go through `write_repository_file` (dirfd, `O_NOFOLLOW`, staged exclusive temporary in `.git`, `renameat`). Regression `rekey_never_writes_through_committed_symlinks` |
| **F-03**: `git mv` preserves old path-bound encrypted blob | Actual Git filter probe, source-level v3 inference | **Must fix v3 UX and data integrity**: standard Git rename must not silently stage an undecryptable record | Test actual `git mv` + `verify-index` + commit + clone + decrypt; implement robust automatic path-rebinding or an explicit safe `mv` that fits ordinary Git workflow; distinguish keyed versus keyless checks; correct user guide immediately | **Fixed**: the pre-commit hook re-encrypts a locally staged `git mv` (files, directories, unprotected→protected) and never re-encrypts content that came from a commit (no laundering of hostile moves); keyless `verify-index` refuses a record that is another path's blob; keyless `audit` refuses a record moved without re-encryption. Tests `renames_are_re_encrypted_for_their_new_path`, `locked_renames_and_unbound_moves_are_refused`, and the hostile-move case in `git_lifecycle` |
| **F-04**: ignored chmod/private-mode failure in clean | Source observation; conditional on existing local plaintext visibility | **Optional local hardening**, not a flaw against public-Git confidentiality when clean correctly stages ciphertext | Do not make clean fail in **default** mode solely because local file permissions are permissive. If strict privacy is enabled, failures must be visible and must fail its claimed guarantee. Keep `doctor` diagnostics truthful | **Resolved**: the default mode no longer changes permissions; in private mode a failed `make_private` now fails the clean filter (`?` instead of `let _`) |
| **L-01**: keyless audit accepts forged v3 envelope | Source-confirmed, accepted A14 | **Explicit external/deployment limitation**; not a valid proof of authenticity | Document that keyless audit detects obvious plaintext/structure, not a valid AES-SIV tag. Do not claim malicious-committer resistance without a keyed/signature-enforcing service | **Accepted conditional guarantee** |
| **L-02**: v2 CBC; v3 same-UID access, weak-password guessing, equality, rollback, hook deployment | Review of documented design | Split: v2 legacy issue; v3 offline-guessing guidance essential; same-UID/equality/rollback are intentional bounds; remote hook is an optional policy/deployment contract | Keep caveats prominent and accurate, and make strict local and server policy features optional; do not expand formalization scope to promise impossible guarantees | **Bounded/accepted; not a blanket security clearance** |

## Second review: adversarial agent review of the new code (2026-10-25)

An independent agent reviewed the product-charter implementation (selection,
stored key, rebind, migration) and reproduced six findings with the
compiled binary: four category-1 (patterns selecting nothing, records moved
to unprotected names, a non-atomic `unprotect`, `migrate` skipping quoted or
local rules) and two usability gaps. All are fixed with regression tests;
see H-34 to H-39 in [V3-SECURITY-REVIEW](V3-SECURITY-REVIEW.md). Its list of
tested non-problems (laundering via `cherry-pick -n`, temporary-index
commits, quoting, symlinked metadata, audit coverage) is kept in the agent
transcript summary there.

## Reviewer instructions and severity rubric

A genuine defect is not waived by calling it outside the original audit's
scope. Prioritize by **consequence to public ciphertext correctness, loss of
recoverable data, unintended writes and normal Git operation**, plus realistic
preconditions. A source-confirmed issue whose Rust CLI was not executed
should be marked **candidate pending reproduction**, not simultaneously
"exploited" and "dismissed". Explicitly distinguish the Bash version and
the Rust version tested.

Local plaintext may be intentionally readable, edited and backed up on the
unlocked machine. An insistence on mandatory memory-only credentials, `0600`
worktrees, private umasks, same-UID isolation or server hooks changes the
product's baseline threat model. Such proposals may be good **optional modes**
but should not be cited as release blockers *merely because they are absent*
in default mode. Conversely, a symlink overwrite on `rekey`, corrupt rename,
unexpected plaintext object or unauthorized decryption **is** in scope.

## Regression and acceptance checklist

- [x] **F-01** actual legacy `git add` + hook test: plaintext beginning
      `U2FsdGVk` is not silently accepted as safe ciphertext
      (`tests/v{2,3}/test_filter_semantics.bats`, `test_pre_commit.bats`).
      No authentication guarantee is claimed for legacy CBC.
- [x] **F-02** real compiled Rust `rekey` test with tracked malicious
      symlinks and an outside sentinel: outside bytes unchanged, config a
      regular file, decryption after lock/unlock works
      (`tests/workflows.rs::rekey_never_writes_through_committed_symlinks`).
- [x] **F-03** real Git `git mv` (file, directory, unprotected→protected),
      `git add` after the move, commit, clone, decrypt; locked move refused;
      unbound `--no-verify` move refused by keyless audit; hostile committed
      move refused, not laundered (`tests/workflows.rs`, `git_lifecycle.rs`).
- [x] **F-04** default encryption succeeds with ordinary local file modes
      (`stored_key_unlock_needs_no_agent_and_follows_the_umask`); private
      mode keeps its 0600 tests and now fails instead of ignoring a chmod error.
- [x] **L-01** the user guide, `audit` output and pre-receive hook say the
      keyless audit stops plaintext, not forged envelopes; keyed audit and
      `verify-index` authenticate every record.
- [x] `cargo test --workspace`, the independent AES-SIV/Argon2id reference
      corpus, and the snapshot provenance were rerun; the source-derived Lean
      build is recorded in [V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md).

**Do not mark a box complete from this documentation-only overlay.** Attach
the actual test, proof, or current-code evidence to the security findings
ledger when the engineering work is done. No existing v3 profile bytes or
Lean proofs are modified by this document.
