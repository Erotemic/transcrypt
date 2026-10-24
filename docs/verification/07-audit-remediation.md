# 07. October 2026 security audit: required closeout matrix

**All findings below are confirmed or identified against the UNRELEASED
October 2026 Bash crypto overlay**, not against the unmodified upstream
`transcrypt-v3` integration branch (which does not implement PBKDF2). No
finding is marked fixed by this documentation-only overlay.

Primary evidence: the October 23 security audit and reproduction script listed
in [sources](reference/sources.md). A future security code change must link
to its test and updated hand-review/proof coverage before closing the row.

| Finding | Severity / scope | Requirements | Required remediation | Regression gate |
|---|---|---|---|---|
| A1: protected ciphertext committed without public config | High, fresh-clone availability | R-10,R-18 | Check staged secure config and staged encrypted blobs as one tree; require committed metadata before commit | G-03,G-04 |
| A2: changed salt accepted with existing ciphertext | High, availability | R-10,R-11 | Reject parameter-only changes or carry out a full re-encryption transaction | G-04 |
| A3: legacy cached plaintext notes/objects remain | High, confidentiality/retention | R-22 | Enumerate all named-context notes; disable future cache writes; give accurate cleanup for reachable/unreachable objects | G-09,G-18 |
| A4: wrong unlock password is persisted before failure | High, availability/recovery | R-16,R-09 | Authenticate before persistent setup; use transactional publication and rollback | G-05,G-12 |
| A5: symlinked `.transcrypt` redirects config writes | High, untrusted repo -> local filesystem | R-17 | Reject symlink ancestors; secure destination creation, race policy | G-06 |
| A6: master/enc keys sent as OpenSSL process arguments | High where argv is observable | R-08 | Redesign Bash primitive invocation so no secret key is in argv; Rust uses in-process primitives; verify platform guarantees | OS-process-argv probes |
| A7: pre-commit magic-only check and newline filename omission | High under filter bypass | R-01,R-15,R-18 | Authenticate staged blobs, enumerate paths via NUL-safe interface; never skip failures | G-07,G-08 |
| A8: repo with prior unencrypted commit selects legacy by default | Medium, downgrade risk | R-12 | Classify by existing crypto objects/metadata, not presence of `HEAD` | G-01,G-02 |
| A9: valid ciphertext transplant within context | Design trade-off | R-04, limitations | Decide path/file-ID binding vs rename support; document permitted substitution and replay | Context/path swap fixture |
| A10: only 64 effective KDF salt bits; default 250k iterations | Parameter review | R-06,R-07,R-25 | Specify minimum 128-bit random public salt input, full transcript, bounded iteration policy; benchmark/select | KDF vectors and resource tests |

## Additional blockers beyond the 10 audit rows

- **B1: custom deterministic cipher construction.** The prototype's
  AES-CBC plus plaintext-HMAC-derived IV and encrypt-then-MAC is not a
  standardized deterministic AEAD construction with an independent security
  review. Match-by-example tests do not settle its cryptographic security.
  Freeze a reviewed algorithm and distinct format discriminator. See
  [02](02-protocol-and-wire-format.md) and [D-01](10-decisions-and-blockers.md).
- **B2: two-implementation feasibility.** The reviewed algorithm must be
  executable correctly from both Rust and Bash's allowed runtime. In
  particular, `openssl enc` does not automatically expose modern AEAD; a
  Python/Rust helper cannot be smuggled into the default Bash dependency
  graph as a hidden fix. See [D-02](10-decisions-and-blockers.md).
- **B3: Git hook bypass.** A hook cannot stop a deliberately bypassed local
  commit. The product's claim must be scoped to cooperative installed
  filters/hooks, with optional remote validation for branch-protection
  guarantees. See [R-01](01-requirements-and-threat-model.md).
- **B4: path races and credential caching.** Symlink checks alone are
  insufficient against a concurrent local actor; and Git filters often run
  without interactive input. The supported platform/adversary model and
  key-handle lifecycle must be designed, not assumed to work.
- **B5: correctness vs security proof.** An Aeneas theorem stating that
  `open(seal(x)) = x` does not imply authenticity, password-guessing
  resistance, privacy of stderr, process isolation, or correct Git staging.
  Proof claims must reference an independent crypto analysis and adapters.

## Required closeout procedure for each finding

1. Preserve the minimal original reproducer as a regression test that fails
   before the change and passes after the change. A test that skips if a
   tool is missing is not considered a pass.
2. Link to the precise code change; explain whether the fix changed public
   behavior, on-disk format, or supported platforms.
3. Update [02](02-protocol-and-wire-format.md) and
   [03](03-git-state-machine.md) if normative behavior was affected;
   never quietly redefine the spec to match a bug.
4. Update the function mapping in [09](09-bash-traceability-and-review.md)
   and independently review the new Bash call sites.
5. Add Rust unit/interop or formal obligations, where applicable, with
   concrete evidence status. A failed proof is not "test-covered".
6. Rerun v2 and v3 suites and the compatibility/fault matrix; include
   complete source, Git and OpenSSL/LibreSSL versions.
7. Security reviewer signs off on the finding; a maintainer's merge alone
   is not a substitute for cryptographic algorithm review.

## Retention warning to ship with migration

Rewriting the current Git tree does **not** guarantee removal of historical
legacy ciphertext, plaintext textconv notes, unreachable plaintext Git
objects, reflogs, backups, remote mirrors, or already exposed passwords.
A migration command may make best-effort local cache hygiene improvements,
but it must accurately report what it did and what remains. Do not perform
unrequested destructive garbage collection that could remove unrelated
unreachable objects. True key compromise requires credential/key rotation
and may require remote and backup remediation.

## October 24 2026 additional staged-tree bypasses and partial A7 progress

**Confirmed, fixed in this development overlay (pending upstream review):**

- A7-index-attributes: the hook previously queried worktree attributes,
  allowing staged plaintext to accompany staged encryption attributes.
- A7-index-mode: the hook previously trusted worktree symlink state,
  allowing staged plaintext regular blobs to be skipped.
- A7-failure-handling: the index file enumerator now reports a failing
  `git ls-files | git check-attr` pipeline instead of silently returning
  zero checked paths; the caller rejects commits on enumeration failure.

**Still open:** the legacy v2 hook recognizes only the unauthenticated
`U2FsdGVk` marker. This cannot establish genuine ciphertext and is not the
final secure-format validation gate. Native Bats and platform matrix remain
mandatory before merging these changes.

- A7-local-override: `.git/info/attributes` overrides staged
  `.gitattributes` even when `git check-attr --cached` is used; the old
  implementation then allowed plaintext. The updated hook consults a
  separate, isolated staged portable-attribute view and unions it with
  the local view. Both exploit and extra-local-protection regressions run
  in `test_staged_index.bats`.
