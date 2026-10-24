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

### M1 (partial) — D-01/D-02 feasibility evidence (OpenSSL 3.0.13)
- **Probe:** `contrib/verification/d02-openssl-cli-probe.sh` (bash+openssl
  only; RFC 7914/RFC 4231/SP 800-38B vectors + pycryptodome-computed
  constants + /proc argv/environ inspection). All checks pass on 3.0.13.
- **Evidence doc:** `docs/verification/reference/d01-d02-feasibility.md`.
  Key results:
  - `enc` exposes no SIV/GCM/CCM; `mac` CMAC is broken on 3.0.13 ⇒
    **RFC 5297 AES-SIV is not implementable in the plain 3.0.13 CLI**
    (D-01: evidence-backed, not decided).
  - `enc -pbkdf2 -iter N -S <8B> -pass file:|fd:` = PBKDF2-HMAC-SHA256
    with **no secret in argv** (verified byte-exact) — but 3.0+ only
    (D-03/D-09 implications; 8-byte `-S` limit).
  - Raw-key AES-CTR/ECB via `-pass file:|fd:` = EVP_BytesToKey(SHA-256)
    expansion, verified byte-exact (D-02).
  - Every CLI keyed-MAC channel (HMAC/CMAC) requires the key in argv
    (D-02; A6 class).
- **CI:** `feasibility-probe` job added to
  `.github/workflows/run-bats-core-tests.yml` (same OS matrix) so the
  capability table is collected per supported platform (Gate B).

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
  maintainer platform policy). The D-01/D-02 evidence they need is now
  available for OpenSSL 3.0.13; **other backends (OpenSSL 1.1.x,
  LibreSSL, 3.1+) are still unprobed** — run the probe in the CI matrix
  and where local access exists; do not assume results.
- M3+ (Bash v3 implementation) waits for a D-01 direction decision.
- M6 (Rust) waits on M1; see 04 for the crate layout.

## Next unblocked task

1. Capture probe results on the remaining matrix backends (OpenSSL 1.1.x,
   LibreSSL, OpenSSL 3.1+) and append them to
   `docs/verification/reference/d01-d02-feasibility.md` (CI job will
   produce them; record verbatim output, do not summarize from memory).
2. Draft the M1 protocol document skeleton
   (`docs/verification/PROTOCOL-DRAFT-*.md`) as an **options paper**
   (SIV wire format for the Rust implementation + the two feasible Bash
   authentication options from the evidence), explicitly marked
   unapproved until D-01 is decided — do not present it as a frozen spec.
