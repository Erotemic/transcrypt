# Independent security assessment — Transcrypt source snapshot

**Assessment date:** 2026-10-25  
**Archive:** `transcrypt-source-2026-10-25T132743-5-861975ad954a.tar.gz`  
**Archive SHA-256:** `c6c2ef606f77565c8bd5333c7e8016ecb05bc4d4b32b090349e4e2d2f8b20ea2`  
**Source commit:** `861975ad954a954aac8a89dea6687c6e7dbc3d0d`  
**Reviewer:** Independent source-level assessment; no participation in the project's internal review  
**Confidence:** High for the v2 plaintext-staging bypass; high for the v3 unsafe rekey-write pattern and POSIX exploit primitive, with the limitation that the compiled Rust v3 command was not run; high for the underlying `git mv` behavior and associated code-level authentication failure.

## Executive conclusion

**Do not treat this snapshot as security-cleared for safeguarding sensitive Git content.** The released Bash v2 path can silently stage plaintext under an easily spoofed magic prefix, even when its pre-commit hook executes. The experimental Rust v3 has an unsafe worktree temporary-file write in `rekey` that can follow a repository-supplied symlink to an external writable file. Its documented rename behavior is also incorrect: `git mv` preserves the old authenticated record rather than re-encrypting it for the new path. A committed rename can subsequently pass keyless checks while being undecryptable under its new path.

These are distinct from the documented v3 cryptographic design limitations. The project's existing internal security review is useful context but does not establish that the unverified adapter is secure; the present assessment reaches its own conclusions from source and independent probes.

## Findings at a glance

| ID | Severity | Scope | Finding | Verification |
| --- | --- | --- | --- | --- |
| F-01 | **High** | Released Bash v2 | Plaintext with an eight-character magic prefix bypasses encryption **and** the pre-commit check | **Reproduced with actual Bash filter and actual pre-commit command** |
| F-02 | **High** | Experimental Rust v3 | `rekey` follows attacker-controlled `.transcrypt/config.rekey` symlinks and can overwrite files outside the repository | **Source-confirmed; POSIX write/rename behavior reproduced**; compiled Rust CLI not run |
| F-03 | **Medium** | Experimental Rust v3 | `git mv` keeps a ciphertext bound to its *old* path; keyed verification fails, but keyless verification may accept it | **Git behavior reproduced with a path-aware filter; v3 outcome follows from source** |
| F-04 | **Low, conditional** | Experimental Rust v3 | Clean-filter file-permission hardening errors are ignored | **Source-confirmed**; exposure requires a plaintext worktree file already readable by others and a failed chmod |
| L-01 | **Accepted limitation** | Rust v3 remote enforcement | Keyless audits accept a syntactically valid but unauthentic forged envelope; they are not cryptographic authenticity checks | **Source-confirmed; explicitly documented by project as A14** |
| L-02 | **Design/deployment risks** | Both versions | v2 CBC without authentication; v3 same-UID agent access, offline passphrase guessing, deterministic equality leakage, and remote-hook deployment dependence | **Source and project threat-model review** |

Severity is qualitative, based on confidentiality, integrity, availability and realistic preconditions; it is not a CVSS score or a claim of remote code execution.

## F-01 — Bash v2 silently publishes plaintext carrying the Base64 salt prefix

**Severity:** High — **confidentiality**.  
**Files:** `transcrypt:427–468`, especially **443–447**; `transcrypt:364–378`, especially **376–377**; `transcrypt:584–630`.

### Root cause

`git_clean()` checks only the first eight bytes of input, and if they equal the literal ASCII string `U2FsdGVk` (the Base64 representation of the beginning of OpenSSL's `Salted__` header), it writes the entire input unchanged. It does not establish that the remaining input is syntactically valid ciphertext, decryptable, or authentic. The pre-commit check independently uses the **same eight-byte predicate** on the staged Git object. This allows a protected file's ordinary plaintext to be mistaken for encrypted data by *both* defenses.

### Independent reproduction

In an isolated Git repository configured with this snapshot's actual Bash clean/smudge filter, the file `token.secret` contained:

```text
U2FsdGVkNOT_ENCRYPTED
private_token=abcdefg
```

After `git add .gitattributes token.secret`, `git show :token.secret` was **byte-for-byte identical** to the worktree file. Both had SHA-256:

```text
d6a4c0f127ca83f6d6707373207234742187c5ee5fd5002ecc9bfd5b1b70fd5b
```

Running this snapshot's **actual** `bash transcrypt pre_commit` returned **success**. This was not a mock pre-commit test. The repository and its contents were disposable test data.

### Threat and impact

A user can inadvertently commit a sensitive file whose first eight characters match the marker, including text derived from Base64 or a deliberately constructed file. A repository adversary can also induce an operator to add such a file. Once pushed, anyone with Git history access can read the plaintext. This finding does **not** depend on breaking AES or guessing a passphrase.

### Fix

Remove the magic-prefix shortcut as a security decision. Only pass through already-encrypted input after strong ciphertext authentication under the expected key and context; prefer versioned AEAD records. Implement the same authenticated gate in pre-commit and enforce an appropriate policy server-side. As a short-term protection, explicitly reject *suspect* `U2FsdGVk`-prefixed data whose ciphertext validity cannot be established; do not silently accept it. Add a regression test using an actual protected file and real hook.

**Incident response:** Audit existing protected objects for unencrypted content, especially prefix-matching blobs; if real credentials reached Git history, rotate them and follow a coordinated history-remediation process rather than assuming a later delete removes exposure.

## F-02 — Rust v3 rekey can overwrite a file outside the repository via symlink

**Severity:** High — **integrity/availability**; needs user to execute `rekey`.  
**Files:** `rust/crates/transcrypt-v3/src/setup.rs:419–478`, especially **463–466**. Related insufficient checks: `rust/crates/transcrypt-v3/src/main.rs:298–315` (checks `config`, not `config.rekey`), **527–564** (`check_index`), and `rust/crates/transcrypt-v3/src/worktree.rs:141–173` (secure staging used elsewhere but not here).

### Root cause

After re-encrypting staged records, `rekey()` does the following in the *Git worktree*:

```rust
let path = root.join(".transcrypt/config");
let temp = root.join(".transcrypt/config.rekey");
fs::write(&temp, config).and_then(|_| fs::rename(&temp, &path))
```

`std::fs::write()` creates or truncates the named file **following symlinks**. The `config.rekey` name is predictable, not opened with no-follow or exclusive-creation flags, and is not checked against the Git index or protected by v3's `*.secret` policy. An attacker who can supply repository contents can commit `.transcrypt/config.rekey` as a symlink to an absolute file path (or to a relative path escaping the checkout). Git can materialize that link on clone/checkout. A victim's later `rekey` will overwrite the link target if the victim has write permission, *then* rename the symlink on top of `.transcrypt/config`.

This is a genuine trust-boundary error: the filesystem adapter treats repository-controlled metadata as a private internal temporary. It is outside the verified core's proof boundary.

### Independent reproduction and qualifications

A POSIX-isolated probe created an external file, placed a symlink at `.transcrypt/config.rekey`, then performed the **same write-then-rename operations**. It confirmed (1) that the external file contents were overwritten and (2) that `.transcrypt/config` became a symlink after rename. This is a reproduction of the OS primitive, **not** a claim that the uncompiled Rust v3 CLI was executed end to end. In source, `verify_index` gates `.transcrypt/config`, `.gitattributes`, and `*.secret` staged entries, but does not gate the additional `config.rekey` path.

An attacker cannot choose all the replacement bytes (the replacement is the new public configuration), and the victim must have unlocked the repository and invoked `rekey`. The demonstrated impact is outside-repository file corruption/denial of service and damage to v3 setup, **not** arbitrary code execution or extraction of the encryption key.

### Fix

Use a checked directory file descriptor for `.transcrypt` and create a genuinely new, unguessable temporary file with `O_CREAT|O_EXCL|O_NOFOLLOW`, mode `0600`; write and `fsync` it, then `renameat` it onto `config`, followed by directory `fsync`. Refuse an unexpected pre-existing `config.rekey` entry, and protect the directory itself from path substitution. Prefer reusing the repository's existing fd-relative `fsat` abstraction, adapted for a public-config atomic replacement. Reject tracked unexpected operational temporaries in `.transcrypt/` as defense in depth. Add a Git-clone-to-rekey symlink regression test targeting an isolated outside file.

## F-03 — `git mv` preserves v3 ciphertext bound to an obsolete path

**Severity:** Medium — **availability/integrity**; no plaintext disclosure demonstrated.  
**Files:** `docs/verification/V3-USER-GUIDE.md:144–148` (incorrect claim); `rust/crates/transcrypt-v3/src/main.rs:527–564` and **576–583**; `rust/crates/transcrypt-v3/src/audit.rs:135–151`; `rust/crates/transcrypt-v3-core/src/lib.rs:649–662`.

### Root cause and independent reproduction

The v3 ciphertext binds its authentication tag to the **exact Git path**. The user guide says, incorrectly, that `git mv` re-runs the clean filter. Git stages a rename by reusing the existing blob object and normally does **not** reapply filters.

An independent test with a real Git repository and a path-aware clean filter created `first.secret`, then ran `git mv first.secret second.secret`. The blob staged at `second.secret` still began:

```text
bound-path:first.secret
```

Only after `git add --renormalize second.secret` did the staged record change to `bound-path:second.secret`. This directly demonstrates the Git semantics on which v3 depends.

A moved v3 record therefore fails AES-SIV authentication at its new path when checked with the key. If the session is **locked**, however, `verify-index` intentionally checks only the record envelope, while keyless `audit` has no means of verifying that the old record is bound to the new name. The invalid rename can thus be committed/pushed in a keyless enforcement scenario and is undecryptable at the new path. Git history may still permit recovery by returning to the old path.

### Fix

Treat protected path renames as a dedicated operation: obtain plaintext using the **old** path, encrypt for the **new** path, stage the new record, and remove the old path. When unlocked, document and test `git add --renormalize new.secret` for simple clean-filter cases, or provide a safe `transcrypt-v3 mv` command. When locked, block or explicitly flag protected path renames as unverifiable rather than suggesting that a keyless envelope check establishes path correctness. Update the user guide immediately.

## F-04 — Worktree plaintext permission-hardening errors are swallowed

**Severity:** Low, conditional (potential confidentiality on shared or unusual ownership setups).  
**File:** `rust/crates/transcrypt-v3/src/main.rs:477–487`.

When the clean filter processes plaintext, it attempts to remove group/other permissions from the corresponding worktree file, but both path lookup and `make_private()` errors are discarded using `if let Ok(...)` and `let _ =`. The clean filter still succeeds and Git stages ciphertext. In a shared checkout, a readable plaintext worktree file that the current user can read but cannot `chmod` (e.g. one owned by another user) remains readable by third parties, with no failure or warning. This risk is partly inherent to user-created files and was acknowledged in project documentation, but silent hardening failure is an avoidable gap.

**Fix:** At minimum warn prominently, and fail the clean operation if file-private permissions are part of the configured security guarantee. Audit existing protected worktree files on `doctor` and avoid promising that every user-created file is automatically private.

## Accepted limitation L-01 — Keyless server-side checks are not authentication

`transcrypt-v3-core/src/lib.rs:649–662` checks only the v3 magic, configuration ID and record length. `audit.rs:135–151` uses this when the authenticating agent is unavailable, including on a keyless remote. An attacker with write access to pushed Git commits can construct bytes with the correct public header and arbitrary tag/body; those pass the keyless format test but fail decryption. This is **not** a new break of AES-SIV. The project explicitly documents it as assumption **A14**, meaning remote enforcement detects accidental plaintext or incorrect framing, **not** malicious corruption, substitution or rollback.

**Action:** Keep this distinction prominent in deployment documentation and status output. For hostile-committer authenticity guarantees, enforce a keyed check in a suitably isolated trusted service or use another reviewed signature/approval policy. Ensure that server-side protection is installed and externally tested; local hooks are bypassable.

## Additional design and deployment observations

- **Legacy v2 cryptography:** `transcrypt:460–466` and **489** call `openssl enc` with AES-CBC and the legacy MD5 password KDF; no MAC or AEAD tag authenticates protected files. Ciphertext corruption and manipulation are not comprehensively detectable. This is an inherent v2 design issue, not a separate exploit demonstrated by this review. `transcrypt:36–51` stores the local passphrase in Git local config by default; protect `.git/config` and its backups accordingly.
- **v3 cryptographic structure:** The reviewed code uses Argon2id and deterministic AES-256-SIV, with the complete public config and exact path as associated data. Its checked core refuses to release plaintext on failed authentication. This is a meaningful improvement over v2, but cryptographic primitive correctness, the effectful adapter and its deployment remain external trust assumptions; formal verification of the core does **not** prove the whole program safe.
- **v3 accepted risks:** Same-UID processes can access the unlocked agent; an attacker obtaining public config can attempt offline passphrase guesses; deterministic ciphertext leaks equality across revisions at one path; the design has no rollback resistance. Remote policy requires server-side enforcement, not only client hooks. The project documents these limitations.
- **Dependency assurance:** Exact version locks and differential test vectors are present. This review did not execute `cargo audit`, check the live advisory database across every transitive dependency, independently assess the AES-SIV crate's internals, or validate compiled cross-platform behavior.

## Testing and evidence

**Executed successfully:**

1. `bash tests/interop/check-bash-legacy-contract.sh` — all supplied released-v2 golden-vector, nonempty-input, corrupted-smudge and marker-contract checks passed.
2. **Additional independent legacy regression:** actual Git clean filter accepted a protected plaintext beginning `U2FsdGVk`; staged blob equaled source; actual `bash transcrypt pre_commit` returned success.
3. **Additional independent Git rename probe:** `git mv` retained the old path-bound clean-filter blob; `git add --renormalize` reapplied the filter for the new path.
4. **Additional independent POSIX symlink probe:** writing the known `.transcrypt/config.rekey` path through a symlink overwrote an outside file; subsequent rename replaced the main config with the symlink.
5. `python3 tests/v3/reference/check_vectors.py -q` — 3 independent AES-SIV reference tests passed.
6. `python3 tests/v3/reference/differential.py` — differential corpus matched independent implementations.
7. `python3 -m unittest -q tests/v3/reference/test_git_filter_paths.py tests/v3/reference/test_git_staged_attributes.py` — 5 additional Git policy tests passed.

**Not executed:** Compiled Rust v3 unit/integration/adversarial tests, the real Rust `rekey` and `verify-index` commands, formal proof build/check, Rust compiler diagnostics, continuous fuzzing, and a true networked remote hook trial. `cargo` and `rustc` were unavailable in this environment. The v3 findings therefore combine direct source inspection with independent tests of OS/Git behavior, not an end-to-end binary exploitation claim.

## Remediation order and acceptance criteria

1. **Block v2 plaintext release.** Remove the `U2FsdGVk`-only short circuit and corresponding pre-commit false assurance. Add a test proving prefix-matching plaintext cannot be committed; audit history and rotate exposed credentials.
2. **Patch v3 rekey's trust boundary.** Use atomic, exclusive, no-follow fd-relative temporary writes, reject unexpected temporary entries, and add adversarial tracked-symlink tests. Fail safely with no external-file change.
3. **Correct v3 rename flow.** Update the documentation, provide tested re-encryption on rename, and ensure locked/keyless checks do not claim renamed records are authenticated at their new paths.
4. **Surface permission failures and deployment gaps.** Make privacy enforcement observable; require a passing `doctor` and verified remote hooks as appropriate.
5. **Repeat review against a rebuilt patched snapshot.** Run `cargo test --workspace`, Rust adversarial and lifecycle suites, full crypto differential checks, proof regeneration, `cargo audit`, and real `rekey`/rename regression tests on supported Unix platforms. Obtain an external cryptographic-library review before claiming v3 production assurance.

### Final assessment

**Two high-severity security issues and one medium-severity data-integrity/availability issue were substantiated by source and independent reproductions**, subject to the stated Rust execution limitation. The positive baseline tests demonstrate that the reference behavior works on selected expected cases; they do **not** negate these negative tests. Current source-level evidence does not support a blanket claim that either implementation, as delivered in this archive, safely enforces secret confidentiality in every supported workflow.
