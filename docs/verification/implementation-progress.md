# Implementation progress

**Maintained per the execution procedure in 08-roadmap-and-pr-plan.md. Short
and factual: current milestone, completed changes with evidence, blockers,
next task.**

Baseline: `elasticdog/transcrypt-v3` @ `fcf94da` + planning-docs commit
(`docs/transcrypt-verification-plan`).

## Current state (2026-10-24)

**M0** — Complete (planning overlay applied; all 11 docs + 2 reference docs).

**M1** — In progress. Feasibility evidence gathering started (see
`reference/d01-d02-feasibility.md` when present). D-01..D-06 remain open
decisions; nothing is frozen.

**M2** — First hardening change landed (see below).

**M3–M10** — Not started (blocked on M1 freeze decisions and M2).

## Completed changes

### M2.1 — NUL-safe path enumeration (branch `work/m2-nul-safe-path-enumeration`)

- **Defect (exists in this working tree; audit class A7):**
  `_list_encrypted_files` converted the NUL-delimited `git check-attr -z`
  stream into space-joined *lines*, then unquoted with `eval`. Filenames
  containing a newline fragmented into bogus paths (`new` / `line`), which
  both `--list` and the pre-commit hook silently skipped. Reproduced: a
  protected file named `new\nline` staged with a **plaintext** blob
  committed successfully (bypass of the pre-commit hook).
- **Fix:** `_list_encrypted_files` now emits a NUL-delimited verbatim stream
  (no line joining, no `eval`); `git_pre_commit`, `list_files`, and
  `show_raw_file` consume it with `read -r -d ''`. `--list`/`git ls-crypt`
  keep their line-based display contract.
- **Tests:** `tests/v2/test_pathnames.bats` (+ identical copy in
  `tests/v3/`): 6 tests (repeated spaces, double-quote, backslash, newline
  pre-commit rejection, repeated-space pre-commit rejection, newline
  round-trip). The two pre-commit tests fail before the fix and pass after.
- **Evidence:** `bats --jobs 4 tests/v2/ tests/v3/` → 176/176 ok (164
  baseline + 12 new); `shellcheck transcrypt` clean; `shfmt -d transcrypt`
  clean; manual before/after bypass repro (plaintext commit rejected after
  fix).
- **Known limitations (documented, not defects):** line-based `--list`
  display of newline names is inherently ambiguous; `--rekey`/`--uninstall`/
  `force_checkout` consume the line-based `git ls-crypt` output and remain
  limited for newline names (follow-up in M5 rework).

## Audit findings vs this working tree (verification per 07)

A1, A2, A4, A5, A8: **not present** in this tree — they are artifacts of the
unreleased October `TCRYPT3` overlay (no v3 config writer, no PBKDF2, no
salt-in-config here). A6: v2 passes the password via child-process
environment (`ENC_PASS`), not derived-key argv; the argv variant of A6 is
overlay-only. A7: the newline-enumeration half **was present** (fixed above);
the magic-only check half is v2's designed check (v2 blobs carry no MAC).
A3: `remove_cached_plaintext` exists (v2 flush/uninstall) — closeout belongs
to M5 migration work.

## Blockers

- M1 freeze: D-01..D-06 need crypto review + maintainer sign-off (external
  gates; not fabricated).
- A3 closeout (M5), A6 redesign (M3) await M1 format decisions.

## Next task

M1 feasibility experiment (D-01/D-02): probe this OpenSSL 3.0.13 CLI
surface (SIV/GCM availability, `kdf` PBKDF2 with file-based secret, raw-key
cipher input without argv secrets, CMAC/HMAC key channels) with process
inspection; record results in `docs/verification/reference/`.
