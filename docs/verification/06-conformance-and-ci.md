# 06. Test vectors, differential conformance, and CI acceptance

**Goal:** prove compatibility empirically across both real distributions and
find errors not modeled by the pure proof kernel. Tests are necessary even
when the Rust parser/policy refinement is complete.

## 1. Who defines expected results?

The source of truth is the frozen independent spec. Publish **fixed golden
vectors** assembled using at least two independently checked calculations,
including relevant standards vectors, with documented provenance. Never
accept "Bash and Rust agree" as sufficient when both could share a bug.
Keep test credentials synthetic and public, never actual repository secrets.

### Required vector dimensions

| ID | Dimension | Expected coverage |
|---|---|---|
| V-01 | Plaintext size | empty; 1 byte; 15/16/17 bytes; many blocks; large streaming case |
| V-02 | Byte content | NUL bytes, all 256 byte values, invalid UTF-8, CRLF and no final LF |
| V-03 | Context | `default`, named context, invalid context names, context swaps |
| V-04 | Metadata | valid canonical; key omissions; duplicate keys; invalid work factor; unknown mandatory fields; changed salt; wrong suite/version |
| V-05 | Password | valid synthetic bytes in supported profile, wrong password, empty/trailing newline, invalid encoding/bounds |
| V-06 | Ciphertext grammar | truncation at every field; capitalization; junk suffix; invalid pad/base64; length overflow; wrong tag; unknown marker |
| V-07 | Determinism | equal plaintext/config/context => identical canonical ciphertext across hosts; distinct context changes record |
| V-08 | Auth and release | modifying any authenticated byte must fail without emitting plaintext or replacing destination |
| V-09 | Version migration | old v2 object read; explicit v2->secure conversion; unsupported modern version fails without downgrade |
| V-10 | Empty authentication | empty protected plaintext seals to approved authenticated record, not bare empty bytes (pending freeze) |

An interoperable secure v3 requires all supported combinations to be
well-specified; unsupported combinations must produce matching *error
classes* even if localized human messages differ.

## 2. Bidirectional interop matrix

For each test fixture, run:

1. Independent reference calculation -> Bash `open` / Rust `open`.
2. Bash `seal` -> Rust `open` -> exact expected plaintext.
3. Rust `seal` -> Bash `open` -> exact expected plaintext.
4. Bash `seal` == Rust `seal` byte-for-byte under identical config/password/
   context/plaintext; repeated calls on each host remain identical.
5. Invalid records -> both reject; stdout empty; no partial file writes.
6. Both programs run in **fresh clones** and normal Git `add`, `checkout`,
   `diff`, `merge` flows, not only direct cipher CLI calls.

Use a deterministic fake RNG only inside test fixtures to generate known
public salt; production must always use an approved entropy source.

## 3. Git integration scenarios

| ID | Scenario | Required outcome |
|---|---|---|
| G-01 | New unencrypted repo with initial commit | Secure init, committed public metadata staged/required, correct fresh clone |
| G-02 | Old transcrypt v2 repository | No format change on ordinary upgrade; migration is explicit |
| G-03 | Fresh clone missing `.transcrypt/config` | Reject before installing poisoned credentials/filters |
| G-04 | Modify only staged `base-salt` or KDF count | Reject if existing blobs inconsistent |
| G-05 | Wrong password then correct password | First fails with no persistent mutation, second succeeds |
| G-06 | Symlink `.transcrypt` to outside repo | No external write, useful error |
| G-07 | Protected newline/tab/unicode filename | Staged validator includes it; no plaintext object accepted |
| G-08 | Counterfeit ciphertext magic and overridden clean filter | Validator rejects unauthenticated staged object |
| G-09 | Named context cached textconv notes | Migration inventories and handles all refs; never creates fresh plaintext notes |
| G-10 | Two or more contexts under migration/rekey | All paths preserved and decrypt with new credential(s) |
| G-11 | Merge conflicts, rename, branch switching, different OpenSSL version | Deterministic objects and documented conflict behavior |
| G-12 | Fault in each migration/init publication step | Either old state works or documented recovery continues; no silently mixed index |
| G-13 | Linked worktrees, `.git` file, alternate index | Correct isolated/common configuration behavior |
| G-14 | `--no-verify` / manually staged blob | Local bypass behavior documented; optional trusted remote verifier detects bad tree |
| G-15 | `git clean`/smudge/process/filter/textconv and hook stderr/stdout | No plaintext leaks to stdout on failure, no diagnostic data contaminates Git protocol |
| G-16 | `git rebase`, `git cherry-pick`, normal merge with same plaintext | No spurious ciphertext changes between supported hosts |
| G-17 | Partial/missing named-context credentials | No silent subset migration or staged inconsistent tree |
| G-18 | Retention/history after rekey | Warnings match reality; legacy history/caches not declared erased |

A cross-version clone/rebase scenario is mandatory because previous PBKDF2
prototypes had reports of divergent ciphertext across OpenSSL versions
([PR #136](https://github.com/elasticdog/transcrypt/pull/136#issuecomment-1208306131)).

## 4. Platform matrix and capability policy

- Linux with representative supported Bash, Git, OpenSSL 1.1.1 and 3.x;
- macOS with supported LibreSSL and optionally Homebrew OpenSSL;
- supported Git for Windows / Bash environment if upstream claims support;
- Rust binary built for each advertised host/architecture;
- environment-specific Git attributes/worktrees/hooks variants.

The **actual supported version matrix and its minimums must be frozen after
running test probes**, not invented from a version number. If Bash lacks the
primitive required by the frozen secure scheme, it must reject secure v3
rather than write weaker ciphertext. A Rust implementation must never emit
ciphertext that the advertised Bash compatibility matrix cannot read.

A job can legitimately be marked *unsupported* only when the compatibility
policy explicitly excludes it. A tool/build missing from CI must never be
reported as a passing verification job.

## 5. CI jobs to add incrementally

1. **Spec lint:** links, requirement ID references, schema example consistency,
   normative-versus-candidate file distinction.
2. **Legacy Bats:** unchanged `tests/v2` behavior and historical fixtures.
3. **Secure Bats:** all new v3 cases, including audit reproductions; no fallback
   to legacy tests masked as v3 coverage.
4. **Rust unit/property tests:** parser, crypto adapter, transaction planner;
   pinned Cargo.lock, no `unsafe` in verification core.
5. **Cross-implementation interop:** every supported Bash/OpenSSL variant
   with Rust; compare exact bytes and both directions.
6. **Git fault-injection:** temporary index, interrupted writes, wrong
   password, lost metadata, named-context notes, symlink/path adversaries.
7. **Rust proof extraction:** regenerate Charon/Aeneas output from pinned
   Rust commit, check absence of unexpected opaque functions, compile focused
   Lean proof targets.
8. **Independent security review gates:** unresolved audit defect table and
   crypto algorithm assessment; not substituted by green functional CI.
9. **Reproducible release:** SBOM/checksums/build provenance and platform
   smoke tests for Rust binaries; no new dependency in Bash packaging.

## 6. Performance and resource limits

Set explicit, reviewed bounds for KDF work factors, encrypted blob length,
config size, number of contexts, and memory/disk temporary buffers.
Measure cold/steady clean-smudge, status, diff, branch checkout, migration,
and multi-file operations. Preserve data from benchmarks; choose numerical
thresholds only from demonstrated target platforms and security goals.

Security takes precedence over a silent performance optimization. Derive-once
key caching, if chosen, must not store keys in public Git config or compromise
the formal separation between credential unlock and crypto operations.

## 7. Evidence classification

Every CI report must distinguish:

- **PROVED:** a named theorem about generated Rust with versioned assumptions;
- **TESTED:** bounded executions on listed hosts/inputs;
- **REVIEWED:** recorded manual Bash mapping or cryptographer decision;
- **ASSUMED:** explicit adapter/primitive/trusted-toolchain contract;
- **UNESTABLISHED:** planned but not yet demonstrated.

No dashboard should collapse these five categories into one green badge.
