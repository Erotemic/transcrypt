# Implementation progress

**Maintained per the execution procedure in 08-roadmap-and-pr-plan.md. Short
and factual: current milestone, completed changes with evidence, blockers,
next task.**

Baseline: `elasticdog/transcrypt-v3` @ `fcf94da` + planning-docs commit
(`docs/transcrypt-verification-plan`). Active branch:
`work/m2-nul-safe-path-enumeration` (stacks on the docs commit).

## Completed

### M0 — Complete
Planning overlay applied (11 docs + 2 reference docs).

### M2.1 — NUL-safe path enumeration (committed `dc2e3ff`)
- **Defect (in this working tree; audit class A7):** `_list_encrypted_files`
  line-joined the NUL check-attr stream and unquoted with `eval`;
  newline-containing filenames fragmented into bogus paths silently skipped
  by `--list` and the pre-commit hook. Reproduced a plaintext-blob commit
  bypass before the fix.
- **Fix:** NUL-delimited end-to-end stream, no `eval`; consumers
  (`git_pre_commit`, `list_files`, `show_raw_file`) use `read -r -d ''`.
- **Evidence:** `tests/{v2,v3}/test_pathnames.bats` (6 tests each; the two
  pre-commit rejection tests fail before / pass after the fix);
  `bats --jobs 4 tests/v2/ tests/v3/` → 176/176 ok; `shellcheck` clean;
  `shfmt` clean.
- **Limitations (documented):** line-based `--list` display of newline
  names is inherently ambiguous; `--rekey`/`--uninstall`/`force_checkout`
  still consume line-based `git ls-crypt` (M5 follow-up).

### M1 (partial) — D-01/D-02 feasibility evidence (OpenSSL 3.0.13 + 3.5.9)
- **Probe:** `contrib/verification/d02-openssl-cli-probe.sh` (bash+openssl
  only; RFC 7914/RFC 4231/SP 800-38B vectors + pycryptodome-computed
  constants + /proc argv/environ inspection + a section-7 kdf value-
  semantics classifier). All checks pass on 3.0.13 and 3.5.9.
- **Evidence doc:** `docs/verification/reference/d01-d02-feasibility.md`.
  Key results (3.0.13 and 3.5.9):
  - `enc` exposes no SIV/GCM/CCM; `mac` CMAC is broken on both ⇒
    **RFC 5297 AES-SIV is not implementable in the plain 3.0/3.5 CLI**
    (D-01: evidence-backed, not decided). 3.5.9 also disproves the
    "3.1+ adds file-keyed kdf" hypothesis: kdf `pass`/`salt`/`secret`
    values are literal text (only `hexpass:`-style key-name prefixes
    decode).
  - `enc -pbkdf2 -iter N -S <8B> -pass file:|fd:` = PBKDF2-HMAC-SHA256
    with **no secret in argv** (verified byte-exact) — but 3.0+ only
    (D-03/D-09 implications; 8-byte `-S` limit).
  - Raw-key AES-CTR/ECB via `-pass file:|fd:` = documented
    EVP_BytesToKey(SHA-256) expansion, verified byte-exact (D-02).
  - Every CLI keyed-MAC channel (mac/dgst `-macopt hexkey`) puts the key
    in argv (D-02; A6 class).
- **Options paper:** `docs/verification/11-crypto-options-paper.md`
  (A: SIV — recommended, with Bash sub-options A1/A2/A3; B: PRF-as-MAC —
  currently not CLI-feasible; C: October prototype — excluded). Unapproved
  by design; the frozen spec follows the external decision.
- **CI:** `feasibility-probe` job added to
  `.github/workflows/run-bats-core-tests.yml` (same OS matrix) so the
  capability table is collected per supported platform (Gate B).

### M6 (partial) — Rust `transcrypt-protocol` core: legacy v2 parser
(roadmap: M6 may partially proceed once the relevant spec slice is
agreed; the v2 slice is the released format, so this is unblocked)
- **New zero-dependency crate** `rust/crates/transcrypt-protocol`
  (builds offline; layout per 04). Implements `detect_format`,
  `parse_v2`, a strict standard-base64 decoder (RFC 4648 vectors,
  residual-bit checks, CRLF-tolerant line breaks), and `V2Record`
  (salt + ciphertext split) with structured errors.
- **Fail-closed discriminator:** a blob with the v2 base64 prefix that
  fails structural validation is `Invalid`, never demoted to plaintext
  (R-03); empty input is `Plaintext` by the released design.
- **Evidence:** 14 tests — unit (RFC 4648 vectors; strictness; hostile
  1 MB inputs incl. NUL/0xff/repeated-prefix/1 MB LCG data; decoder
  vs encoder agreement) plus a **differential test** that builds real
  v2 blobs with the Bash pipeline's exact openssl commands and checks
  the Rust parser's split against it (salt equality, ciphertext
  decrypts via the Bash pipeline, truncation fails closed).
  `cargo test --offline` and `cargo clippy` clean.
- **Out of scope until D-01:** any v3 grammar, key derivation, or
  decryption (those live in the future crypto adapter; this crate must
  not define the secure format by example).

## Audit findings vs this working tree (per 07)

A1, A2, A4, A5, A8: not present — artifacts of the unreleased `TCRYPT3`
overlay (no v3 config writer, no PBKDF2, no salt-in-config here).
A6: v2 passes the password via child env (`ENC_PASS`), not derived-key
argv; the argv variant is overlay-only. A7: fixed above (newline
enumeration); the magic-only check itself is v2's designed check.
A3: v2 flush/uninstall cache removal exists; full closeout is M5.

Additional observation (candidate finding, not yet classified):
`transcrypt.crypt-dir` (attacker-writable in `.git/config` of a cloned
repo) redirects `save_helper_scripts` `mkdir`/`cp`/`chmod` outside the
git dir; `add_pattern`/`sed_inplace` write through `.gitattributes`
symlinks. Needs a decision on the `crypt-dir` override policy before any
fix (compatibility impact on shared-gitdir workflows).

## Blockers

- M1 freeze: D-01..D-06 are external decisions (crypto review,
  maintainer platform policy). Evidence for D-01/D-02 now covers OpenSSL
  3.0.13 and 3.5.9; **OpenSSL 1.1.x and LibreSSL remain unprobed**
  (the CI `feasibility-probe` job will produce those; record verbatim
  output when it runs). LibreSSL expectations: no `kdf`, no `mac` app,
  no `-pbkdf2`; `enc -pass file:/fd:` + legacy ciphers available —
  confirm, don't assume.
- M3+ (Bash v3 implementation) waits for a D-01 direction decision.
- M6 (Rust) is **partially** unblocked: the legacy v2 parser slice is
  done; the secure-format parser/serializer, policy crate, crypto
  adapter, and interop suite all wait on the frozen v3 spec (M1).

## Next unblocked task

1. Once CI (or any 1.1.x/LibreSSL host) produces probe output, append it
   to `docs/verification/reference/d01-d02-feasibility.md` verbatim.
2. The options paper (11) is ready for the external D-01 decision; when a
   direction is chosen, write the frozen `PROTOCOL-<id>.md` from it, then
   continue M6 in `rust/` (v3 parser/serializer, policy crate) and M3 in
   Bash from that single spec.
3. No further Bash v2 hardening is known in this tree beyond the A7 fix
   (see audit cross-check above); the `crypt-dir`/symlink-redirect
   observations are queued for a maintainer decision before any fix.
