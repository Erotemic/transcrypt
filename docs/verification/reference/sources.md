# Evidence and provenance register

Every upstream statement below is tagged as an *agreement*, *preference*,
*discussion*, or *candidate code*, so a planning proposal is not misrepresented
as maintainer approval.

## Upstream contributions and discussions

| Link | Evidence | Interpretation |
|---|---|---|
| [Issue #134, May 18, 2026, contributor](https://github.com/elasticdog/transcrypt/issues/134#issuecomment-4468026156) | Public salt independent of password; versioned config; PBKDF2; authenticated modern format; migration; safe failures | Contributor's stated desired direction, **not** final approval of an algorithm |
| [Issue #134, May 18, 2026, maintainer](https://github.com/elasticdog/transcrypt/issues/134#issuecomment-4478657672) | Seven-step small PR series against `transcrypt-v3`: read settings, duplicate tests, PBKDF2, v3 tests, write settings, migration, hardening | Agreed development sequence and scope; explicit no Python dependency in default Bash distribution |
| [PR #209 review](https://github.com/elasticdog/transcrypt/pull/209#issuecomment-4478751477) | Prefer short actionable notices instead of public `--audit` and `--diagnose` commands; disallow insecure new-format configurations | Maintainer preference; use errors/notices in init and migration |
| [PR #210 review](https://github.com/elasticdog/transcrypt/pull/210#issuecomment-4554871791) | Target `transcrypt-v3` instead of main to keep stable branch open to bugfixes | Upstream release/process constraint |
| [PR #211](https://github.com/elasticdog/transcrypt/pull/211) | Split Bats suites for v2 and v3 | Already merged into the integration branch |
| [PR #219](https://github.com/elasticdog/transcrypt/pull/219) | Draft integration PR | Base commit for this documentation overlay |
| [PR #136 comment on salt](https://github.com/elasticdog/transcrypt/pull/136#issuecomment-1168232291) | Prefer fresh salt on rekey; preserving old one should not be the default | Historic shared preference, not a final frozen protocol decision |
| [PR #136 on CLI defaults](https://github.com/elasticdog/transcrypt/pull/136#issuecomment-1179609024) | Secure new defaults are desirable but legacy cloning requires careful compatibility | Historical compatibility requirement |
| [PR #136 portable-test issue](https://github.com/elasticdog/transcrypt/pull/136#issuecomment-1208306131) | Earlier PBKDF2 prototype had cross-machine checkout/conflict issues | Strong evidence that exact cross-version vectors and Git workflows are release gates |
| [PR #136 LibreSSL feedback](https://github.com/elasticdog/transcrypt/pull/136#issuecomment-1475263316) | Capability detection differs between OpenSSL and LibreSSL | Do not infer support only from version-number parsing |
| [PR #132 discussion](https://github.com/elasticdog/transcrypt/pull/132#issuecomment-1120333389) | Consider derive-once vs derive-per-file and separate written algorithm | Unresolved design tradeoff, not a decided optimization |

Earlier #132/#136/#162 are superseded/defunct work. They can supply test
cases but must not be used to override the 2026 incremental plan.

## Available local evidence, status not proof

- User-supplied source archive: `transcrypt-source-2026-10-23T184339-5-76f00e1ef1f4.tar.gz`.
- October 2026 proposed implementation overlay:
  `transcrypt-v3-authenticated-pbkdf2-final-overlay.tar.gz`.
- October 23 security audit:
  `transcrypt-v3-security-audit-2026-10-23.md`, with reproductions in
  `transcrypt-v3-audit-repros.sh`.
- An exploratory `transcrypt-verification-foundation` working tree exists,
  but it was not included in this documentation-only overlay. Its Rust code
  and Lean source must not be treated as compiled or proved merely because
  they are present.

## Standards and tool documentation

- [RFC 5297: AES-SIV](https://www.rfc-editor.org/rfc/rfc5297.html):
  standardized deterministic authenticated encryption candidate.
- [RFC 5869: HKDF](https://www.rfc-editor.org/rfc/rfc5869.html):
  key-derivation domain separation reference.
- [OpenSSL `enc` documentation](https://docs.openssl.org/master/man1/openssl-enc/):
  explicitly does not support authenticated modes such as GCM/CCM.
- [Git gitattributes/filter behavior](https://git-scm.com/docs/gitattributes):
  clean/smudge, `required`, worktree/index conversion behavior.
- [Charon manual](https://aeneasverif.github.io/charon/manual/):
  Rust to LLBC.
- [Aeneas capability and limitations](https://aeneasverif.github.io/aeneas/):
  current restrictions; prove only supported extracted functions.
- [Aeneas getting-started guide](https://github.com/AeneasVerif/aeneas/blob/main/documentation/getting-started.md):
  current Charon/Aeneas/Lean workflow, subject to pinned-toolchain checks.
- [Kani Rust Verifier](https://model-checking.github.io/kani/):
  auxiliary bounded checking, not replacement for complete Lean refinement.

All links should be reviewed again at protocol freeze. Dates and feature
support change; CI uses pinned and recorded versions, not `main` by default.
