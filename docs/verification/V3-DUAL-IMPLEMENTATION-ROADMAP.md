# Transcrypt v3: Bash/OpenSSL and Rust parity program

**Status:** Updated 2026-11-11. The first independent Bash v3 **profile-2**
reference implementation exists at `contrib/v3/transcrypt-bash`, with exact
independent byte vectors and basic Git lifecycle tests. Rust P2/P3 support,
full cross-backend parity, formal extension, and OpenSSL 3.0.13 qualification
remain outstanding. This plan supersedes the *deferral* of Bash v3 in earlier roadmaps;
it does not supersede the byte-exact, frozen
[profile-1 specification](specs/V3-AUTHENTICATED-P0.md) or the existing
[Rust proof ledger](V3-PROOF-COVERAGE.md).

**Target:** two independent v3 implementations of the same published protocol
and ordinary Git user workflows. The Bash distribution runs with Bash, Git,
standard Unix utilities and the **OpenSSL 3.0.13 CLI**; no Rust binary,
Python, compiled helper or custom OpenSSL library is required. Rust supports
all portable profiles **and retains its stronger existing Argon2id profile**
and optional hardened local execution. On a shared profile, both clients
produce **identical authenticated Git objects** and make the same
security-relevant decisions. Empirical tests establish the Bash
correspondence to the independent specification and source-derived Rust/Lean
models; the Rust proofs **do not** prove the Bash source.

Read with the [product charter](V3-PRODUCT-CHARTER.md),
[active roadmap](V3-ROADMAP.md), [Bash crosswalk](V3-BASH-CORRESPONDENCE.md),
[profile-1 wire contract](specs/V3-AUTHENTICATED-P0.md), and
[feasibility correction](reference/d01-d02-feasibility.md).

## 1. Product contract and trust boundary

Transcrypt is **encryption for publication in Git**. The principal adversary
can read the public repository, all reachable and historical Git objects,
committed configuration, and encrypted blobs, and can provide altered,
truncated, replayed or transplanted records. The adversary does not have the
passphrase or an unlocked developer machine. For supported profiles, the
important outcomes are:

1. A selected protected file's published Git blob is authenticated
   ciphertext, including empty and binary files, instead of recoverable
   plaintext. A Git filter bypass, interrupted staging, missing filter or
   disabled hook cannot be silently presented as a protected publish.
2. Incorrect passwords, modified/config-swapped/other-path records and
   malformed/unknown versions are rejected without releasing unauthenticated
   plaintext; there is no legacy/downgrade or plaintext fall-through.
3. The cost of an offline dictionary attack is set by the **chosen profile
   and password strength**. Public salt and parameters are committed. The
   default portable profile should retain a memory-hard KDF.
4. Correctly configured and unlocked repositories support ordinary Git
   editing, add, commit, checkout, merges, rebases, renames, rekey, lock and
   recovery without corrupting data or changing ciphertext semantics.
5. Both implementations authenticate the exact Git-relative path bytes and
   committed configuration, preserve deterministic ciphertext, and explain
   limitations (filenames, sizes, equality, history replay, old plaintext
   commits and deliberate policy bypasses).

**Local environment assumption.** The developer's unlocked workstation is
normally trusted. Plaintext in the worktree and derived keys in process
arguments, environment, Bash variables, local files or memory do not by
themselves violate the publication threat model. No special process-isolation
or secure-zeroization theorem is required of the portable backend. Rust may
provide such features for a stricter local threat model. Do not manufacture
blocking safeguards, tests-of-tests or proof goals solely to eliminate an
accepted local exposure. **Local data crossing into committed Git state**
(including staged temporary files, a credential accidentally added to Git,
plaintext notes and filter failure) *is* a publication-security defect.

The threat model assumes an honest/competent operator using the configured
workflow; a malicious committer with unrestricted Git commands can bypass a
local hook. `audit`/pre-push checks are useful but keyless envelope detection
cannot prove cryptographic authenticity and cannot guarantee enforcement at
a remote without a deployed server-side policy. New histories do not erase
old plaintext history. No deterministic per-blob scheme prevents rollback of
an old valid revision without external freshness information.

## 2. Profile families and capability negotiation

The **committed `.transcrypt/config` determines the complete suite**. An
implementation must parse the exact discriminator, validate the configuration
and advertised parameters, then check that its installed backend can execute
the selected suite **before unlock, Git filters, staged edits, migration,
rekey or any mutating operation**. Read-only inspection can describe an
unsupported profile. An unknown or unsupported profile must fail clearly,
not substitute another algorithm or allow a plaintext write.

| Planned profile | KDF | Authenticated encryption | Bash + OpenSSL 3.0.13 | Rust | Status |
| --- | --- | --- | --- | --- | --- |
| **P1 — preserved Rust** | Argon2id v19, m=65536 KiB, t=3, p=1, 64-byte output | AES-256-CMAC-SIV (RFC 5297), path/config AAD | Not supported by 3.0 CLI KDF | Existing | Frozen `TCFG3 00 01` / `TV3F 00 01` |
| **P2 — portable preferred** | scrypt (fixed `N,r,p,maxmem`, 32-byte salt, 64-byte output) | Same AES-256-CMAC-SIV construction and AAD contract | Target | Implement | **Implemented in Bash**; profile-2 bytes and parameters documented in [P2 spec](specs/V3-PORTABLE-P2.md); Rust pending |
| **P3 — portable fallback** | PBKDF2-HMAC-SHA256 (fixed work factor, 32-byte salt, 64-byte output) | Same AES-256-CMAC-SIV construction and AAD contract | Target | Implement | **Implemented in Bash**; profile-2 bytes and parameters documented in [P2 spec](specs/V3-PORTABLE-P2.md); Rust pending |

P2 is the intended **Bash default** once memory and time are benchmarked on
OpenSSL 3.0.13. P1 remains available and may remain the Rust default; do not
auto-convert it to P2. P3 is a supported compatibility choice, not a silent
fallback from P2. Retain every Rust-only stronger option. Newer OpenSSL
implementations may unlock P1 or further suites **only** after byte-for-byte
proof-of-capability on that actual CLI and a review of its KDF and SIV
composition; a version string alone is insufficient. Compatibility describes
*capabilities*, not a moral ranking of implementations.

P2 now uses frozen experimental bytes `TCFG3 00 02` and `TV3F 00 02`,
with KDF `scrypt(N=32768,r=8,p=1,dkLen=64)` and 32-byte salt; see the
[P2 wire contract](specs/V3-PORTABLE-P2.md). P3 remains a planning label. Future profiles require new discriminators and their own reviewed wire contracts. The existing 55-byte P1 config,
22-byte file header, salt, domain separation, path byte rules and key-check
semantics stay unchanged. Other profiles may reuse the general layout **only
if** the independently frozen spec assigns unambiguous bytes and KDF
transcripts; never reinterpret P1. Include profile identity and all public
KDF parameters in authenticated config, and bind the entire config to the
file record. Profile switching is an explicit full re-encryption/rekey
transaction, with a rollback and compatibility plan for existing clones.

### CLI capability matrix (target, not a completed certification)

- OpenSSL 3.0.13 `mac -cipher AES-256-CBC -macopt hexkey:... CMAC` was
  reported working on the target machine on 2026-11-11. `-cipher AES-256`
  was the incorrect earlier CMAC probe. AES-SIV is *not* an `enc` mode:
  Bash must compose the standard RFC 5297 S2V/CMAC and AES-CTR steps.
- OpenSSL 3.0 `kdf` exposes `SCRYPT` and `PBKDF2` with `hexpass:` and
  `hexsalt:` parameters, plus explicit 64-byte output. Keys/passwords in
  CLI arguments are accepted local exposures. Check precise 3.0.13
  semantics with known-answer vectors and runtime probes; do not rely on
  OpenSSL 3.5-only behavior. `enc -pbkdf2 -S`'s eight-byte salt interface
  is **not** the planned derivation: retain the full 32-byte repository salt
  via the KDF CLI.
- OpenSSL 3.0 exposes AES-256-CTR for the SIV encryption half. Test the
  SIV-specified counter-bit masking, arbitrary binary inputs and lengths.
- OpenSSL 3.0 does **not** expose Argon2id in `kdf` (added in later 3.x).
  Profile P1 remains Rust-only on the target machine.
- A build lacking a required provider/algorithm is unsupported. Probe the
  actual commands, key sizes, encoding, exit codes and outputs at startup
  or first use; never downgrade to CBC/MD5, an unauthenticated mode, a
  lower KDF work factor, or an alternate output encoding.

The portable script can call system `git`, `openssl` and common Unix tools;
record the exact required utilities and supported Bash/Git versions when
building the compatibility matrix. Avoid optional `xxd`, Python, Perl,
Rust, or another cryptographic executable as an implicit dependency; a
standard utility may be required only when explicitly listed/tested. Bash
cannot store NUL bytes in variables: carry ciphertext, binary paths and
intermediate S2V blocks using binary-safe streams/files/descriptors, and
make any password-byte restrictions explicit in the frozen profile grammar.

## 3. User-visible parity and intentional divergence

**Parity means executable, two-direction acceptance tests**, rather than
matching help text or having commands with similar names. For profiles both
clients support, test:

| Area | Shared required behavior |
| --- | --- |
| Setup & compatibility | `init`, `unlock`, `doctor`, `status`, config/profile inspection, unsupported-suite errors, persistent local unlock by default |
| Selected paths | `.gitattributes` and nested rules, arbitrary binary Git paths, exclusions, non-UTF-8 names, empty/binary/executable files |
| Filters | Clean, smudge, checkout, switch, diff and merge; byte-identical ciphertext and authenticated plaintext for all portable-profile vectors |
| Stage/publication | Pre-commit repair/verification, pre-push and `audit`, bypass/failed-filter cases, keyless and keyed diagnostics |
| Git workflows | `git add`, commit, restore, stash, rebase, conflicted merge, `git mv` rebinding, partial and interrupted operations without data loss |
| Lifecycle | `protect`, `unprotect`, `lock`, `hydrate`, `rekey`/profile conversion, `uninstall`, fresh clone, linked worktrees, explicit v2 migration |
| Robustness | Wrong password, wrong config/path/profile, tampering, garbage, truncated/oversized records, symlinks, permission errors, crashes, locked state |

Make a capability table in the user-facing `doctor`/profile commands: Bash
on OpenSSL 3.0.13 can decline P1 while Rust can open it; both can open P2/P3
when implemented. Switching clients for an already supported repository
must not require re-encryption. If Git's locally configured filter command
points to an unavailable backend, the command must fail safely and explain
how to install a compatible backend; a new clone installs **its own** local
filter driver after profile validation. The committed config must never
require a Rust binary on a Bash-portable profile.

**Intentional differences:** Rust can retain `--private`, private agent,
secret-zeroization/argv discipline, stronger filesystem/process hardening
and optimized long-running filter process. Bash may use local argument
secrets and a simpler per-file filter, with a performance penalty. Such
differences are permitted if they do not change public objects,
authenticated acceptance, selected-path policy or data recovery. Any
user-visible Rust feature lacking a Bash counterpart must have either a
portable implementation plan or an explicitly labeled Rust-only local
hardening exemption; do not call general missing Git features "parity".

## 4. Formal assurance aimed at consequential outcomes

The Rust/Lean program should prove **source-derived decisions used by the
running Rust executable**, under named cryptographic and Git/OS adapter
assumptions. Priority obligations, per supported profile:

1. **Exact decode/dispatch:** unambiguous version/profile/parameter parsing;
   unsupported, malformed, mismatched, or corrupted records cannot be
   accidentally dispatched through a weaker or legacy path.
2. **Authentication gate:** only authenticated plaintext from the exact
   config and Git path can reach an accepted decrypt/smudge/hydrate decision;
   wrong key/config/path/tag rejects without plaintext output.
3. **Publish gate:** for protected staged paths, accepted output is a valid
   authenticated envelope under the selected profile. Model absent Git
   filters/hooks, rebind after rename, staged attributes, index-to-commit
   transfer, and where local hooks alone cannot enforce publication.
4. **Transition/recovery:** init, rekey, profile switching, migration,
   protect/unprotect, lock and failed/crashed operations preserve either a
   usable prior state or an explicit recoverable state, without silently
   creating plaintext publication or losing the last copy of edits.
5. **Cryptographic composition:** encode the S2V/CTR construction, ordered
   AAD, domain separation, 32-byte salt use and KDF parameter selection in
   the independent spec; prove the production-derived *composition logic*
   against it where practical. State conditional confidentiality/integrity
   claims using independently reviewed AES-CMAC-SIV and KDF assumptions.
   No claim of proving OpenSSL or RustCrypto primitive implementations is
   implied by these Lean results.

Extend the existing `no_std` extracted Rust core and Lean definitions instead
of replacing the proof architecture with duplicate hand-written models. A
new suite must not lower previous P1 proof coverage. Each proof obligation
has a concrete user-observable security or recoverability consequence, a
production Rust call site, theorem name, test vector and explicitly
separated remaining assumption in [proof coverage](V3-PROOF-COVERAGE.md)
and [assumptions](V3-ASSUMPTIONS.md).

Bash **does not inherit** the Lean theorem. Its assurance is independent
RFC/NIST vectors, byte-for-byte Rust differential tests, Git integration
and fault tests on real executables, traceable review of Bash functions and
failure paths, and agreement on observable policy decisions. Agreement
increases confidence that the Bash implementation follows the same intended
security design; it does not establish source-level Bash verification.

## 5. Work packages and exit criteria (ordered)

| Stage | Concrete work | Exit evidence |
| --- | --- | --- |
| **D0 — decisions & target** | Update charter, feasibility register and compatibility policy; declare 3.0.13 baseline and optional local exposure; freeze P1 unchanged | Docs agree; `openssl mac` CMAC probe corrected |
| **D1 — primitive feasibility** | Build a disposable Bash/OpenSSL 3.0.13 CLI spike for 64-byte scrypt and PBKDF2, CMAC/S2V and AES-CTR, including binary-safe I/O and error handling | Independent RFC 5297/NIST and KDF vectors; exact output, failure and performance numbers on target host; correct probe script |
| **D2 — new profile spec** | Independently fix profile IDs, KDF salt/params/domain, config tag, file header/AAD, key check, acceptance and migration rules; add profile registry | Reviewed spec, cross-language test fixtures covering successful/invalid inputs; P1 unchanged |
| **D3 — Rust multi-profile** | Implement P2/P3 dispatch, KDF adapters, SIV reuse, profile-aware config/authentication, structured unsupported-profile errors and explicit conversion | Rust vectors and real-Git regression suite green; P1 vectors bit-identical; no implicit downgrade |
| **D4 — formal extension** | Extend production-core extraction and independent Lean spec to profile dispatch, auth/publish decisions and conversions; reconcile assumptions | Compiled source-derived theorems, drift check, updated proof ledger per profile |
| **D5 — standalone Bash v3** | Add Bash portable profile config reader, crypto layer, commands, Git integration and clean/fail behavior without Rust dependency | Independent vectors; one full Bash-only repo from init through clone, edit, rekey, migration and audit |
| **D6 — parity & adversarial matrix** | Run Bash→Rust and Rust→Bash alternating writes and workflow transitions; bad inputs, fault injection, Git variations and platform matrix | All common-profile feature rows pass in both directions; documented hardening exemptions and remaining issues |
| **D7 — qualification & UX** | Benchmark process-heavy Bash vs Rust, document supported backends, profile selection and errors, reconcile all older docs, obtain outside cryptographic/security review | `doctor` self-checks, user guide, CI and review records; no unsupported claims |

Implement D1 before inventing an alternative cipher. Start with SIV and
scrypt; add PBKDF2 only after exact CLI round trips are demonstrated. Work
packages can overlap, but format IDs and security assertions are not final
until D2. A failing primitive probe should change the capability matrix or
lead to an explicit new profile proposal; it must **not** silently weaken P1
or the portable profile.

### Conformance matrix required to claim parity

- **Byte vectors:** fixed password/salt/config/path/plaintext; compare full
  config bytes, 64-byte derived key, key-check and entire ciphertext; both
  directions and repeatability; empty, binary, long and boundary inputs.
- **Adversarial vectors:** wrong password, cross-profile config, config
  replacement, path transplant, truncation, wrong tag, prefix collision,
  malformed lengths, unsupported profile, oversized data and malicious Git
  path names. Compare structured outcome classes, not diagnostic prose.
- **Git interoperability:** Bash init → Rust unlock/update → Bash checkout;
  reverse; mix `protect`, `rekey` and profile migration with an old clone;
  verify staged-tree bytes and a new clone, including branch transitions and
  merge/rename across protected paths.
- **Publish boundary:** deliberately omit filters, bypass hooks, make a
  driver fail, use unconfigured clone, stage conflict data and fake an
  authenticated header. Check that advertised safeguards actually refuse
  the relevant plaintext and identify server-policy limitations.
- **Recovery:** injected kill and command failure at transaction boundaries,
  symlink and path races, unchanged original edits, clean recovery and no
  undeclared temp files staged into Git.
- **Environment:** actual OpenSSL 3.0.13 target, CI for a second OpenSSL 3.x
  provider combination, Linux/macOS where supported, GNU/BSD tool
  differences, and Git version matrix. Do not label 3.5 testing as 3.0.13
  coverage.

Store the case inventory as machine-readable fixtures with a clear source:
independently checked cryptographic vectors, plus cross-implementation
expected outcomes. Run the same scenarios against both CLIs. Include a
feature matrix listing `passing`, `unsupported intentionally (profile/local
hardening)` or `missing`, backed by test IDs. **No percentage or blanket
parity claim from duplicated v2 Bats tests.**

## 6. Key constraints and implementation pitfalls

- Keep P1 exactly intact. Do not change Rust's existing config/header
  discriminators, Argon2 settings or derived-key storage semantics to
  accommodate Bash.
- Do not confuse `openssl enc`'s lack of AEAD with lack of CMAC. Use the
  correct `openssl mac -cipher AES-256-CBC ... CMAC` invocation and compose
  SIV carefully, including S2V zero-length and long-message cases.
- Do not use `openssl enc -S`'s short salt field as the v3 repository KDF
  salt. Do not use legacy MD5 `EVP_BytesToKey` as an accidental fallback.
- `openssl kdf -kdfopt hexpass:...` and MAC `hexkey:` expose material in
  command arguments. Accept that for ordinary local Bash operation, but
  ensure it is absent from Git objects and from diagnostics captured to
  committed files. Never echo a password to the user by default.
- Bash shell strings and `$(...)` cannot transport NUL safely. Use streams,
  binary files or descriptors for bytes, validate subprocess exit status,
  and keep all temporary paths out of the index and worktree publication
  boundary.
- Path binding makes `git mv` and merge transitions security-relevant;
  rebind at the target Git path rather than ignoring authentication failure.
- The frozen profile's independent wire spec, not either CLI's accidental
  output, decides how a discrepancy is repaired. Mark actual defects and
  maintain separate test/proof/evidence ledgers.

## 7. Definition of complete

Bash-only users on OpenSSL 3.0.13 can initialize, unlock, edit, commit,
clone, merge, rename, audit, rekey and migrate a portable-profile repository
without installing Rust. Rust users can perform the same operations on that
repository, see the **same ciphertext bytes**, and optionally choose P1 and
stricter local hardening. A P1 repository opened with Bash 3.0 reports
`unsupported profile` before mutating anything; the reverse direction
(P2/P3 into Rust) works without migration. Each important publication and
recovery property has a source-derived Rust proof or a clearly identified
external assumption, and a corresponding Bash empirical conformance case.
Any residual feature differences are explicit capability distinctions or
failing items, not hidden exceptions to the parity claim.

## Implementation checkpoint (2026-11-11)

- **D1/P2:** The `openssl kdf` SCRYPT control is lowercase `n:`; `N:` was
  rejected by testing. AES-SIV is assembled using `openssl mac` AES-CMAC
  and `openssl enc -aes-256-ctr`. Eight independently generated Python
  scrypt/AESSIV byte vectors pass with OpenSSL 3.5.5, including non-UTF-8
  paths, 0/1/15/16/17-byte messages, and binary data. Run the same suite
  on the maintainer's OpenSSL **3.0.13** to qualify that target.
- **D2/P2:** The profile-2 wire contract and experimental discriminators
  are recorded in [V3-PORTABLE-P2.md](specs/V3-PORTABLE-P2.md). P1 is
  unchanged. P3 remains a proposal.
- **D5 (partial):** Bash can initialize, install filters/hooks, unlock,
  protect/unprotect, encrypt/decrypt, lock, hydrate, rebind after rename,
  rekey, verify staged blobs, audit committed trees with current or
  historical keys, reject plaintext intermediate commits through pre-push,
  and run diff/merge drivers. The [Bash guide](../../contrib/v3/README-BASH.md) lists limitations.
- **Still required:** D3 Rust P2 implementation; D4 proof extension; D5
  Bash v2 migration and conflict/clone robustness; D6 bidirectional Rust
  conformance and publication fault matrix; D7 target-version and platform
  qualification. Do **not** claim empirical feature parity yet.
