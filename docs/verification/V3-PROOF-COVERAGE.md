# Transcrypt v3: proof and test coverage ledger

**Updated 2026-10-24.** This ledger prevents a compiled proof, a functional
regression, an extraction check, and a cryptographic assumption from being
reported as the same kind of evidence. See the active [v3 roadmap](V3-ROADMAP.md).

Evidence levels:

- **PROVED (source-derived):** a compiled Lean theorem explicitly names a
  Charon/Aeneas-generated production Rust function in its proposition.
- **SPEC PROVED:** compiled theorem about the independent Lean model only.
- **TESTED:** real Rust/Git tests, independent reference tests, or user-reported
  builds, with the tested revision recorded in the relevant commit/CI log.
- **GENERATED:** extraction/snapshot integrity and compilation; this does not
  imply functional refinement.
- **TRUSTED / REVIEW:** external operation or security property outside Lean.
- **OPEN:** no sufficient evidence yet.

| ID | Requirement / theorem target | Current evidence | Remaining work |
| --- | --- | --- | --- |
| W-00 | Generated Lean matches actual Rust v3 codec source | **GENERATED**, `SNAPSHOT.json`, snapshot hash/CI regeneration checks; user confirmed this pipeline builds and pushed it | Maintain on every codec change |
| W-01 | Actual extracted config/file magic matches independent specification | **PROVED (source-derived)**; three compiled theorems in `V3Wire/Verification/Refinement.lean` (per user's successful build) | Maintain only; not the whole codec |
| W-02 | Actual config encoder serializes all 55 bytes, arbitrary valid salt and tag | **OPEN**; encoder extracted | Generated `encode_config` RustM success and full-field theorem |
| W-03 | Actual exact config decoder accepts iff magic/length/fields valid | **OPEN**; decoder extracted; independent shape facts proved | Generated `decode_config_exact` success, errors and bounds |
| W-04 | Actual file-header encoder serializes all 22 bytes, arbitrary ID | **OPEN**; encoder extracted | Generated `encode_file_header` full-field theorem |
| W-05 | Actual file-header decoder rejects wrong magic and extracts ID exactly | **OPEN**; decoder extracted | Generated `decode_file_header_exact` proof |
| W-06 | Public Rust slice parsers reject short/overlong inputs correctly | **TESTED**, Rust core unit tests; not currently among the four extracted fixed-size targets | Extract/prove boundary or explicitly keep as tested adapter precondition |
| C-01 | Deterministic Argon2id + AES-SIV v3 bytes match independent vectors | **TESTED**, `tests/v3/reference/check_vectors.py`, Rust vector tests; user confirmed latest build/test cycle worked | External algorithm/security review and environment assumptions |
| C-02 | Authenticated config, ordered path-bound AAD, no plaintext release on failed authentication | **TESTED / TRUSTED**, pure adapter and negative-path tests, Python path-substitution tests | Extract invoked precondition/authorization logic, prove it against abstract AEAD contract; review actual library usage |
| G-01 | Initialize, clone, unlock/hydrate, clean, commit, lock, re-unlock | **TESTED**, Rust Git lifecycle suite; user-confirmed fixes | Define exact trusted Git/FS semantics and failure boundaries |
| G-02 | Staged index bytes/paths validated, not HEAD; symlink/path and path-transplant rejection | **TESTED**, lifecycle, raw `%f`, and effective staged-filter-attribute checks, including local/nested overrides | Targeted adversarial fault/race tests and invoked decision proof |
| G-03 | Crash-safe, atomic multi-file updates | **OPEN**; per-file temp/rename and preflight are implemented | Harden/journal or narrow guarantee; add interrupted-lock/hydration tests |
| G-04 | Derived key absent from disk while unlocked | **TESTED / DESIGN**, private credential agent and restricted socket | Same-UID/socket, swap, crash and zeroization threat review; not Lean-proved |
| B-01 | Standalone Bash conforms to authenticated v3 spec | **OPEN / DEFERRED**; existing Bash maintains legacy modes | Separate Bash port, review and common vectors; no false proof inheritance |
| R-01 | Independent algorithm, threat and adapter security review | **OPEN**; AES-SIV dependency warns it is unaudited | Review before claims about production security |

## Current compiled Lean coverage is narrow

- **Actual generated code:** `proofs/aeneas/v3/V3Wire/Extraction/Funs.lean`.
- **Independent specification:** `proofs/lean/Transcrypt/V3Wire.lean` and
  `proofs/lean/Transcrypt/V3WireCodec.lean`.
- **Actual current correspondence theorems:**
  `extracted_config_magic_matches_spec`,
  `extracted_file_magic_matches_spec`, `extracted_magic_disjoint`.
- The independent `decode_config_encode` and `decode_file_header_encode`
  theorems are **SPEC PROVED**. They do *not* assert anything about the
  Aeneas-generated encoders/decoders.
- Aeneas output being compiled and file hashes matching is **GENERATED**, not
  a proof of the four functions' behavior.

The selected security suite's computational security, library implementation,
and the effectful Git/OS code remain a separately reviewed trusted boundary.
The word "verified" must always say **which obligation**, **what theorem or
test**, **which code revision**, and **which trust assumptions**.

## Minimal completion gate — do not expand proof scope gratuitously

- [ ] W-02 through W-05 each have a compiled theorem referring to the **actual
      extracted Rust function**; the public length boundary W-06 is covered
      by proof or an explicitly declared tested adapter contract.
- [ ] An invoked pure production Rust decision seam has proof obligations
      corresponding to C-02 and G-02; the proof names the same functions the
      running adapter calls, not disconnected test/policy code.
- [ ] All Rust v3 unit, Git integration and independent crypto vectors pass;
      CI rebuilds tracked Lean and re-extracts for drift; adapter assumptions
      documented and reviewed. Production-release review R-01 remains
      independent of this **formalization** gate.

On each new theorem or material adapter change, update this table and
`proofs/aeneas/v3/PROOF-STATUS.md` in the same commit. Do not include routine
`#print axioms` or mass theorem inventories in normal Lean builds.

### Staged attribute override boundary (2026-10-24)

The `verify-index` Rust adapter now checks **the effective `filter` attribute
for every protected staged Git pathname** using `git check-attr --cached -z
--stdin filter`, parsing exactly three NUL-delimited fields per request. This
catches local `.git/info/attributes`, nested staged `.gitattributes`, and
checkout/index attribute divergence that a byte comparison of the root
`.gitattributes` alone cannot catch. It rejects wrong filter values before
any staged secret is decrypted. Staged metadata itself must have mode 100644.

**Evidence status:** independent *real Git* attribute-precedence tests are
passed locally; compiled Rust lifecycle tests are the acceptance gate on the
user's toolchain. Git's interpretation of attributes and absence of concurrent
same-UID modification are trusted external assumptions; a `--no-verify`
commit can bypass any local pre-commit hook. This is **not** a new Lean proof.

The `CodecSteps.lean` workbench targets three actual Aeneas-generated loop
body definitions, including per-byte writes for arbitrary input bytes. These
obligations are **candidates**, not counted as PROVED or imported into the
normal tracked proof build until the focused Lean target compiles. W-04 and
W-05 remain OPEN pending whole-loop theorems.
