# 01. Requirements, security goals, and threat model

**Document status:** historical requirement set from the earlier dual-Bash/
Rust design campaign. Some requirements (mandatory two-way Bash parity,
local-credential threat assumptions, path-binding choices, and release gates)
conflict with the updated 2026-10-25 maintainer direction. The authoritative
*current product and threat model* is
[V3-PRODUCT-CHARTER](V3-PRODUCT-CHARTER.md). The separate v3 byte spec still
controls actual authenticated bytes. Keep the legacy R-01–R-28 IDs for
traceability; do not silently treat every line below as a live blocker.

## 1. Product requirement

Transcrypt allows designated Git-tracked paths to have plaintext in an
authorized working tree while Git stores encrypted bytes. Contributors may
clone, branch, merge, rekey, and migrate without accidentally mixing formats,
losing access to encrypted material, or silently disclosing plaintext. Two
interchangeable implementations (Bash and Rust) must interpret each released
protocol version identically, including errors.

The Bash distribution uses its existing runtime dependencies (shell, Git,
OpenSSL/LibreSSL) only; the Rust distribution may link its libraries into a
standalone binary. The Rust presence, compiler, proof checker, and Rust package
manager are never prerequisites for installing/running Bash Transcrypt.

## 2. Assets and parties

- **Assets:** plaintext protected files; repository encryption password and
  derived keys; local Git config and credential handles; committed public
  cryptographic configuration; encrypted Git blobs and historic Git objects;
  repository integrity and ability to decrypt after clone.
- **Authorized collaborator:** knows the applicable secret for at least one
  encryption context, uses an accepted binary, can inspect a trusted repo.
- **Repository recipient without the secret:** obtains all committed public
  metadata, Git history, blob lengths and ciphertext, names and contexts.
- **Active repository adversary:** may create malicious branches, malformed
  ciphertext/config, submodules, symlinks, filenames, or staged objects,
  replay old commits, and cause a user to clone/pull those changes. Cannot
  initially read a collaborator's secrets.
- **Local observer:** depending on OS permissions, can inspect process argv,
  environment, temporary files, process lifetime, and shared directories.
  Stronger guarantees against same-user privileged malware are *out of scope*.
- **Concurrent workspace actor:** another process modifying files/index
  during an operation. Concurrency assumptions must be made explicit and
  tested; pure Bash may not offer atomic no-follow primitives on every OS.
- **Toolchain adversary:** compromised compiler, Rust crates, OpenSSL, Git,
  or proof generator. This is outside a pure Rust/Aeneas functional proof;
  supply-chain mitigations are additional controls, not theorem consequences.

## 3. Formal security objectives

### Secrecy, cryptography, and accepted output

| ID | Required property | Acceptance evidence |
|---|---|---|
| R-01 | For a recognized encrypted path, successful `clean` writes only valid authenticated ciphertext to the staged Git object; arbitrary plaintext is never the intended successful result | Pure spec, staged-object tests, effect adapter review |
| R-02 | Failed authentication, malformed ciphertext, unknown format, wrong password, or missing metadata produces a nonzero failure with no *partial* plaintext on stdout or in output files | Parser theorem + streaming/failure-injection tests |
| R-03 | A byte-exact format discriminator selects one and only one decoder; no fallback or downgrade after v3 parse/authentication failure | Decoder proof and negative corpus |
| R-04 | Decrypted plaintext and authenticated associated data correspond to the bytes that the approved encryption algorithm committed to | Crypto contract + validated implementation |
| R-05 | Equal plaintext under the same key/context and supported associated data yields equal stored ciphertext, by design, unless format parameters explicitly change | Canonical vectors and round-trip/determinism theorem |
| R-06 | Password-derived key material is context/domain separated; public salts are generated independently of passwords and never reused accidentally across fresh repositories | KDF transcript spec, tests, RNG contract |
| R-07 | New-format cipher suites must be authenticated and meet a separately reviewed security definition for deterministic encryption; functional proofs alone cannot assert this | Algorithm standards, review, rationale and design approval |
| R-08 | Neither distribution knowingly places passwords/derived keys in process argv, logs, trace output, public Git metadata, or crash diagnostics for new-format operations | OS process audits; secrets-handling design |
| R-09 | Secret material is not available to uninitialized clones unless an explicit unlock succeeds; local saved credentials follow an intentional consent/persistence policy | Threat review and key-handle tests |

### Versioning, metadata, and Git state

| ID | Required property | Acceptance evidence |
|---|---|---|
| R-10 | The staged tree containing v3 ciphertext contains the complete, parseable, compatible public configuration for the corresponding context(s) | Staged-index invariant + fresh-clone tests |
| R-11 | Edits to cryptographic config that invalidate staged ciphertext are rejected; legitimate changes use an explicit full-tree migration/rekey transaction | Config-state theorem + test scenarios |
| R-12 | New non-legacy initialization is secure-by-default without misclassifying ordinary Git repositories with existing commits as legacy-encrypted | Initialization classification matrix |
| R-13 | Existing legacy encrypted repositories remain readable without silently re-encrypting or changing their committed bytes during a normal upgrade | Historical fixtures + full v2 Bats suite |
| R-14 | All collaborators can discover the version/suite from committed metadata and ciphertext; unsupported implementations fail with a useful diagnostic | Cross-version clone tests |
| R-15 | Git attributes, filters, and hooks use byte-safe paths and cover filenames with newlines, tabs, spaces, unicode, and leading dashes | NUL-delimited path tests |
| R-16 | A failed init/unlock/migrate/rekey does not strand credentials, leave broken filters, or leave an inconsistent staged tree; crash recovery is explicit | Transition spec + fault injection |
| R-17 | Public-config writes cannot silently follow attacker-controlled symlinks outside the allowed destination or overwrite arbitrary existing files | Filesystem adversary tests and adapter review |
| R-18 | The security validation decision is computed from *staged* config and *staged* ciphertext, not an unrelated working-tree view | Index snapshot test; alternate-index tests |
| R-19 | Protected empty files have a specified authenticated representation or a documented, reviewed exception; absence of bytes is not casually treated as authenticated emptiness | Format-case vector, negative tests |

### Migration, retained data, and operational safety

| ID | Required property | Acceptance evidence |
|---|---|---|
| R-20 | Migration preserves plaintext content and intended contexts for all protected paths or reports failure without committing a mixed tree | Multi-context migration scenarios + model |
| R-21 | Rekey rotates cryptographic keys and normally regenerates the public salt; it does not retain old keys or silently weaken parameters | Rekey matrix; new vs old credential tests |
| R-22 | Migration disables creation of plaintext Git textconv caches and inventories/handles legacy notes for every context; it never claims to purge unobserved backups/history | Audit tests; explicit retention notice |
| R-23 | Migration, rekey, and unlock treat `git worktree`, linked Git dirs, symbolic attributes, dirty index/worktree, and conflicts explicitly rather than guessing | Environment matrix + transaction tests |
| R-24 | Security diagnostics are actionable and do not contaminate filter stdout | Golden stdout/stderr tests |
| R-25 | Malformed/attacker-chosen config values have bounded parsing/runtime costs (KDF iterations, lengths, allocation, integer overflow) | Parser proof + resource tests |
| R-26 | The CLI's capability detection tests actual supported commands/operations, not only command exit codes or version text | OpenSSL/LibreSSL compatibility tests |
| R-27 | Both distributions implement the *same released byte format and state semantics*; a version-specific feature that one cannot implement is not silently accepted by the other | Bidirectional suite + compatibility manifest |
| R-28 | Every security property is classified as proved, conditional-on-trusted-adapter, tested, manually reviewed, or unestablished | Evidence ledger in CI artifacts |

## 4. Explicit security limitations

These are not waived requirements; they bound honest claims.

1. **Deterministic encryption leaks equality and approximate plaintext size**
   within a key/context/AD domain. A standard deterministic AE scheme does
   not provide ordinary randomized IND-CPA security for arbitrary low-entropy
   predictable plaintext. The release must document this clearly.
2. **Repository history is not authenticated as fresh** by a per-blob MAC.
   Valid ciphertext/config from an old trusted commit can be replayed if an
   attacker controls which commit a user sees. Protecting freshness needs a
   separate trusted monotonic state or signed-history policy; not planned
   for the first interoperable format.
3. **Path substitution/rename**: default proposal intentionally avoids
   binding ciphertext to the current filename to preserve Git rename and
   merge semantics. Valid same-context ciphertext substitution is not
   prevented by per-blob authentication alone. See decision [D-08](10-decisions-and-blockers.md).
4. **Existing compromised secrets remain compromised** after merely
   changing a KDF setting. Migration does not erase old Git objects, caches,
   remote copies, passwords in backups, or external snapshots.
5. **Git hooks are bypassable** (e.g., by an intentionally nonconforming
   committer). Hooks protect cooperative local workflows, not enforce a
   repository-wide security policy against an authorized adversarial writer.
   Remote policy or a separate server verifier is needed to enforce it.
6. **Compromised local machine/OS and same-user malware** can typically
   read data once it is decrypted. Neither Rust nor Lean fixes that.
7. **Cryptographic primitives and host effects** remain assumptions unless
   separately verified. Stated functional refinements do not mathematically
   establish computational confidentiality, absence of timing leakage, or
   atomicity of the underlying filesystem.

## 5. Adversarial test classes

The conformance suite must include these inputs, not only ordinary roundtrips:
malicious config changes; absent config; incorrect password; invalid MAC;
truncated/wrong-version envelopes; oversized iteration counts; paths with
embedded newlines; symlinked `.transcrypt`; Git alternate index; stale
textconv notes; encrypted blobs supplied under wrong contexts; mixed-version
histories; unclean worktrees; interrupted migration; legacy-to-modern
upgrades with both default and named contexts; empty and binary files.

The [state-machine document](03-git-state-machine.md) defines expected behavior
for these cases, and [audit closeout](07-audit-remediation.md) tracks the
known October 2026 reproductions.
