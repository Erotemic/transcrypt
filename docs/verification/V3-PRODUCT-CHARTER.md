# Transcrypt v3: product charter, security promise and non-goals

**Status:** Maintainer-directed product intent, recorded 2026-10-25. **Authority:**
this is the source of truth for the *intended product and threat model*, not
an assertion that the current Rust implementation already satisfies it.
The [byte-exact v3 protocol specification](specs/V3-AUTHENTICATED-P0.md)
continues to govern **existing v3 ciphertext**. Nothing in this charter
retroactively changes a wire format, proves an implementation, or approves a
security-sensitive release.

**In one sentence:** Transcrypt lets a reasonably informed developer select
files to keep encrypted **in a public Git repository and its history**, while
working with ordinary plaintext in their **unlocked local checkout** as
naturally as if Git encryption were not there.

## 1. The promise and its boundary

The user chooses which paths are protected. With an adequately strong
passphrase, a correctly configured and initialized checkout, and Git invoking
the installed filters as specified:

1. **The selected files' committed Git blobs are authenticated ciphertext,**
   not plaintext, and deterministic re-encryption produces stable bytes for
   unchanged content under the same config and pathname.
2. **Decryption is exact or fails.** It returns the authenticated plaintext
   for the expected repository/config/path, or rejects the record without
   releasing unauthenticated plaintext. Errors never silently select a weaker
   format or downgrade to a plaintext pass-through.
3. **Normal local Git operations are uneventful.** After unlocking once, edit,
   diff, stage, commit, check out, switch, merge, rebase and rename protected
   files with little or no Transcrypt-specific ceremony. Losing the only copy
   of an edit is an implementation defect, not a permissible usability cost.
4. **The guarantees are stated precisely and checked against actual code.**
   The independently specified Rust protocol/decision core is the formal proof
   target; cryptography, Git invocation, OS effects and proof translation are
   explicit, maintained assumptions until they are narrowed or discharged.

The principal adversary is an **offline reader of all public Git objects,
committed config, histories, and copies of the public repository**, without
the passphrase or local-only credential. It may also supply corrupt, forged,
truncated or transplanted records for the program to process. It must not be
able to elicit accepted, unauthenticated plaintext through an implementation
mistake.

This is **encryption for publication**, not encryption of the developer's
unlocked workstation. A user who can already read local plaintext, the local
credential or the user's processes is *not* the adversary this product
primarily defends against. Likewise, an informed user with unrestricted Git
access can deliberately turn off a filter, commit a plaintext file, or share
the passphrase. The product does not attempt to make such choices impossible.

The promise does **not** cover files the user did not select, an unconfigured
clone that has not installed the filters, data already committed in plaintext,
plaintext copied to an arbitrary unrelated filename, or an actively malicious
committer bypassing locally installed policy. These distinctions must be
visible in the user guide, not hidden in a security appendix.

### Security guarantees are conditional, never absolute

A machine-checked refinement theorem about production-derived Rust is a
strong, valuable guarantee **about its stated model**. It is not a proof of
all of Git, RustCrypto, the OS, Charon/Aeneas, the compiler or the entire CLI.
No document or agent may claim "no bugs" or "completely formally verified"
without a theorem and trusted-boundary statement sufficient for that claim.

Offline passphrase attacks remain possible; Argon2id increases their cost but
cannot rescue a weak password. Passphrase quality is ultimately the user's
choice: make strong generation and clear guidance easy, and support stricter
organizational policy as an option. Do not claim a weak chosen passphrase is
strong merely because the encryption code is formally verified. The public still learns filenames, commit
structure, approximate record sizes and deterministic equality. Previously
published secrets remain published. Authenticating a blob does not prevent
replay of an old valid Git revision without external freshness state.

## 2. First-class goals (in priority order)

| ID | Goal | Concrete acceptance test |
| --- | --- | --- |
| G1 | Correct authenticated public-Git ciphertext | For every *selected and configured* protected path, ordinary staging produces authenticated, path/config-bound v3 bytes; no plaintext can be emitted on authentication failure; independent vectors agree |
| G2 | Arbitrary protected file selection | **Git `.gitattributes` is the selector.** Patterns can cover `.env`, credentials, directories, extensions or individual files. No hardcoded `*.secret` restriction in the protected-path core, Git operations, auditor or UX. Selection can be inspected and tested using Git's actual attribute semantics, including staged history and raw pathname bytes |
| G3 | Invisible everyday use | Unlock once per checkout; later ordinary Git commands work without manual hydration, agent restarts, enforced private umask or recurring password prompts. Renames and merges remain usable; interrupted operations preserve edits |
| G4 | Persistent local unlock **by default** | Store a repository-scoped **derived key**, not the passphrase, in **local-only Git state** across process exit/reboot. `.git/config` is an acceptable simple place; a private sidecar referenced by local Git config is also possible if it is demonstrably simpler or safer without losing UX. Neither is version-controlled or public metadata. No daemon is required for normal use |
| G5 | Optional stricter local mode | Keep the memory-only credential agent, session expiration, no-persist mode, private file permissions and related hardening **optional** for users who want them. Both credential modes use the identical v3 ciphertext format and policy |
| G6 | Source-derived formal assurance | Actual invoked Rust v3 code, translated with pinned Charon/Aeneas, refines an **independent** Lean spec for serialization, authentication gates, path binding, and consequential security decisions; keep the residual trusted boundary enumerated |
| G7 | Recoverable, explicit legacy transition | Provide a tested **one-time** Bash/v2-to-v3 migration that preserves intended protected files, warns about older history, and fails without losing plaintext or mixing states. No need to support v2 ciphertext in the formally verified v3 runtime |
| G8 | Clear Bash correspondence | Maintain a command/semantics mapping to Bash Transcrypt, and independent conformance vectors. A future *Bash v3* may implement the same approved protocol if feasible, but Bash v3 parity is **not** a prerequisite for a good Rust v3 product |
| G9 | Simplicity, portability, performance and truthful security reporting | Reduce required components, implicit states, ritual and incidental failures; benchmark real Git flows; rank remaining assumptions and actual attacks, not arbitrary theorem or commit counts |

The order reflects product value, not permission to release before serious
cryptographic and adapter review. A verified core plus unaudited adapters is
not by itself a production certification.

### Protected-path selection: the planned contract

Git's attributes, including nested attributes and their precedence, define
which *committed or staged* paths are protected; a `protect PATTERN` helper
may manage those entries. For example, the eventual workflow should allow:

```gitattributes
.env                 filter=transcrypt-v3
config/credentials.* filter=transcrypt-v3
private/**           filter=transcrypt-v3
```

Do not implement a second incompatible glob engine in Rust. Authenticate
the **exact canonical Git-relative path bytes** selected by Git. Check
staged-tree and effective-attribute consistency where required, while keeping
intentional user opt-outs possible. The audit must evaluate what was selected
at the relevant commit, not merely glob today's worktree with `*.secret`.

**Changing the policy is a transition**, not an excuse to leave previously
tracked plaintext in history silently. Supply an intelligible conversion path
and inspectable diagnostics. Git's filter invocation and remote hooks are
external contracts; do not promise a guarantee for an unconfigured clone.

**Implementation status:** implemented after `d8436c6` (Git-attribute
selection with the `transcrypt` macro, `protect`/`unprotect`, per-commit
attribute evaluation in `audit`, a suffix-free verified path policy). See
[A16/A19](V3-ASSUMPTIONS.md) for what is proved, tested and assumed.

### Credential behavior: the planned contract

`unlock` authenticates once and stores a scoped derived key locally. Subsequent
Git filters obtain that key without prompting and without requiring an
always-running background service. Local credential persistence has the same
confidentiality implications as an unlocked checkout, by design. A derived
key can decrypt the repository and deserves explicit handling, but a user
choosing persistent mode has intentionally accepted that local risk.

Do **not** store the passphrase or key in a committed `.transcrypt/config`,
Git history, process argv or debug output. If the derived key is stored in
`.git/config`, document that `git config --list`, support bundles or copied
`.git` directories may expose it; a private sidecar is an alternative, not a
reason to reimpose a daemon. Neither option strengthens the protection of an
already compromised local machine. A memory-only agent remains a valid
optional mode, not the required/default architecture.

**Implementation status:** implemented after `d8436c6`. The derived key is
stored in a private sidecar, `$GIT_COMMON_DIR/transcrypt-v3/key` (0600, not
in `git config`, shared by worktrees). This was chosen over `.git/config`
because it is equally simple and is not shown by `git config --list`. The
memory-only agent and private worktree permissions are the optional
`--private` mode. See [A17/A6](V3-ASSUMPTIONS.md).

## 3. Non-goals and deliberately optional protections

| Not a default security requirement | Why / preferred treatment |
| --- | --- |
| Confidentiality of **unlocked local plaintext** against other programs or local users | The user intentionally works with plaintext. Honor ordinary filesystem behavior by default; optional private mode can enforce `0600`, a private umask and restricted process/agent lifetime |
| Preventing an informed user from bypassing Git hooks, editing attributes, or intentionally staging plaintext | Explain selection and operational consequences; **do not** turn ordinary local use into a frustrating policy enforcement system |
| Remote/server hook deployment as a prerequisite to using Transcrypt | Offer `audit`, CI and server hooks for organizations that want enforcement. Explain that a keyless envelope audit detects obvious plaintext, **not** cryptographic authenticity or hostile forgeries |
| Same-UID malware resistance or an OS privilege boundary for the user's own processes | Outside the ordinary-unlocked-worktree threat model; special isolation is an opt-in advanced product |
| Rollback prevention for old valid Git revisions | Requires trusted freshness/signatures outside a deterministic per-blob authenticated-encryption protocol |
| Concealing filenames, sizes, Git commit graph or deterministic equality | Intrinsic limitations of the chosen Git-oriented design; document them |
| Adding legacy CBC/MD5 encryption to the proved v3 core; full legacy CLI parity | Use the old tool only for explicit migration; keep the new protocol narrow and authenticated |
| Formal verification of all RustCrypto, Git, the compiler, OS or Lean itself | State narrowly bounded external contracts, run adversarial tests and obtain independent reviews; formalize only when it removes a consequential implementation assumption |
| Broad cipher agility, multiple credential contexts, GPG integration or elaborate privilege management *by default* | Consider based on demonstrated user value; not a condition for a simple secure v3 release |

**Non-goal does not mean "ignore concrete defects."** A symlink-based
out-of-repository overwrite, incorrect rekey transaction, silent plaintext
staging due to a Git parser bug, or `git mv` leaving an undecryptable record
are **implementation errors**, even when local plaintext privacy is outside
scope. Fix errors that violate authenticated-public-Git correctness,
recoverability or ordinary user expectations. Optional privacy controls must
provide what they claim when enabled; failed enforcement cannot be silently
reported as success in that mode.

## 4. What independent reviewers should assess

First identify the asset, attacker, required precondition, affected version
(Bash v2 versus experimental Rust v3), and actual consequence. Classify the
finding in one of the following **separate** buckets:

1. **Must fix for the advertised v3 promise:** plausible public plaintext
   release via ordinary configured Git, invalid acceptance of unauthenticated
   records, path/config mixups, attacker-controlled writes outside the intended
   repository, loss/corruption of recoverable data, or normal Git workflow
   silently producing undecryptable records.
2. **Optional local hardening:** plaintext worktree mode `0644`, same-UID
   agent access, idle timeout, `mlock`, local shell history exposure unrelated
   to committed objects. These merit accurate docs and opt-in features, **not
   default workflow blockers** unless they also cause a category-1 bug.
3. **Deployment/policy:** cooperative hooks, CI, malicious committer policy,
   signed commits and remote enforcement. Keep the enforcement guarantee
   explicitly conditional on adoption.
4. **Protocol limits / trusted primitives:** dictionary attacks on weak
   passphrases, deterministic equality, old-history replay, external crypto
   libraries, OS and translator assumptions. Report precisely; do not label
   the unavoidable limit a flaw in a correctly implemented protocol.
5. **Legacy-version vulnerabilities:** real Bash v2 issues remain real and
   may warrant fixes, migration notices and incident response, but do not
   cause an expansion of the formally verified v3 runtime with legacy crypto.

A review can discover something serious that the current model missed. This
charter is not permission to dismiss reproducible attacks that violate the
stated public-Git security goal; it is a way to distinguish them from demands
for a different product. See the [October 25 independent assessment triage]
(V3-REVIEW-TRIAGE.md) and its [source report]
(reviews/2026-10-25-independent-source-assessment.md).

## 5. Formalization and assumptions: proof discipline

- Maintain the **independent byte/specification authority**. Do not adjust a
  theorem or spec to bless an unexpected implementation behavior.
- The proof claim is conditional and function-specific: identify real Aeneas
  definitions, theorem names, inputs, success/error outcomes, and calls in
  the production adapter. Compiled models of adapter sequencing are not a
  machine-checked refinement of the entire adapter.
- Keep [V3-ASSUMPTIONS](V3-ASSUMPTIONS.md) and
  [V3-PROOF-COVERAGE](V3-PROOF-COVERAGE.md) current. Record explicit
  exceptions for `Git`, `OS`, `RustCrypto`, `Argon2id`, `AES-SIV`, random
  generation, `Charon/Aeneas`, and compiler/toolchain provenance.
- When changing selection semantics or credential access, move the reusable
  security decisions into the production Rust `no_std` core and update
  source-derived Lean correspondence. Do not try to prove the user's chosen
  filenames or local machine security.
- Evidence classes remain distinct: source-derived Lean proof, Lean model,
  real-Git tests, independent crypto implementation, manual code review,
  externally trusted assumption, and explicitly accepted risk.
- Unknown or incomplete correspondence stays **OPEN**, never implicitly
  promoted by a passing integration test.

## 6. Transition, evolution and release

1. **Legacy v2 transition:** decrypt/verify using the old implementation;
   preserve a safe copy of the plaintext; select patterns for v3; perform a
   deliberate full conversion and staged-tree check; verify a fresh v3 clone
   can decrypt; only then retire old credentials. Do not silently rewrite old
   Git history or pretend old ciphertext inherits v3 security.
2. **Bash correspondence:** document what a Bash user can do in Rust v3 and
   what materially differs. Same-profile Bash v3 is an optional independent
   implementation, not the definition of the Rust product.
3. **Versioning:** a backward-incompatible change to the authenticated
   ciphertext/config transcript must get a new discriminator/profile and
   explicit conversion. A credential-storage option or pattern selector need
   not affect the wire format if its authenticated inputs do not change.
4. **Release:** independent review remains important for a security product.
   An internal agent cannot declare an independent crypto audit completed.
   Release gates should test the *declared* security promise, not invent an
   unrelated local-at-rest requirement.

## 7. Work priorities and continuity rule

**Near-term priority:** (a) independently reproduce/fix genuine v3 adapter
and transaction bugs, notably reviewed rekey-symlink and path-bound rename
failures; (b) implement arbitrary Git-selected paths; (c) default to
persistent local unlock with optional private mode; (d) make ordinary Git
flows transparently correct; (e) source-derive the generalized security
contract and its Lean refinements; (f) provide recoverable v2 transition.
Independent security review, performance and portability run in parallel.

A completed task, proof milestone or clean audit is a **checkpoint**, not a
campaign-completion rule. After each improvement, look again for a meaningful
advance in correctness, simplicity, usability, portability, security or
formal assurance; take the best next action. Do not manufacture unnecessary
complexity, regress verified guarantees, or label missing external audit as
code completion. If the current execution must end, leave a precise, tested
handoff rather than declaring the product finished.

**Interpretation precedence:** maintainer's current product direction and
this charter govern goals/non-goals; the frozen wire spec governs committed
bytes; actual checked source, test/proof results and known findings govern
current implementation claims. Older numbered roadmaps, internal reviews and
agent prompts are historical inputs and cannot silently override these
priorities.
