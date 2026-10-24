# Released Transcrypt v2 — byte-exact interoperability contract

Status: **baseline contract for legacy compatibility**. This describes the
released `transcrypt` Git filters as amended by the accompanying Bash fixes.
It does **not** approve the legacy cryptographic design or define the future
secure v3 protocol. The latter requires an independent, reviewed specification.

The reason to write down this existing format first is practical: it lets the
Bash implementation, Rust alternative, independent vectors and future Lean
specification agree on precisely what an old repository means. The pure
functions in `rust/crates/transcrypt-legacy-core/src/lib.rs` operate on these
bytes, not on a duplicate model assembled for an SMT tool.

## 1. Domain and inputs

- `P`: bytes read from Git **clean stdin**, or stored ciphertext from **smudge
  stdin**, or bytes read from the requested `textconv` file. Filenames or
  worktree file sizes are not an authority for the content of `P`.
- `F`: verbatim Git `%f` path bytes, relative to Git's worktree as supplied
  to the filter. Do not normalize Unicode, path separators, or whitespace.
  On Windows use the path encoding supplied by the supported Git adapter;
  non-reversible encodings must fail rather than silently change the salt.
- `W`: local (private) password bytes for the selected context. Credentials
  are loaded from `transcrypt.password` or `transcrypt.<context>.password`.
- `C`: cipher name in the corresponding local configuration, usually
  `aes-256-cbc`; v2 permits other ciphers, including stream modes.
- `context`: `default`, or a name matching `[a-z](-?[a-z0-9])*`.
  A named context selects separate local cipher/password settings, never a
  different v2 envelope grammar.

This is **legacy context selection**, not authenticated public metadata.
Never interpret `.transcrypt/config` values describing a new crypto suite as
permission to decrypt using v2.

## 2. Deterministic salt and encryption

For nonempty clean plaintext that does not begin with the v2 passthrough
marker:

```text
K = F || 0x3a || W                            # bytes, ASCII colon
D = HMAC-SHA256(key=K, message=P)            # 32 digest bytes
S = D[24:32]                                 # final 8 bytes
E = OpenSSL enc -e -<C> -md MD5 -S hex(S)
    -pass env:ENC_PASS                        # ENC_PASS = W, legacy only
    on stdin P, with OpenSSL's historical EVP_BytesToKey rules
B = ASCII("Salted__") || S || E
Output = RFC4648_base64(B) with lines of 64 characters
         and a final LF (for nonempty B)
```

Here `E` means the **ciphertext**, excluding any `Salted__ || S` header that
an older OpenSSL/LibreSSL `enc -S` may prepend. The Rust adapter always
constructs `B` itself. This avoids having to infer format from the OpenSSL
version string. Cipher padding and length constraints belong to the selected
cipher adapter, not the `transcrypt-protocol` envelope parser.

The key/IV derivation and cipher security are delegated to the OpenSSL legacy
adapter. They are **not** proved by the pure Rust core. v2 uses unsalted-fast
MD5-era expansion after its 8-byte salt and provides **no ciphertext
authentication**. It is retained solely for old repositories.

## 3. Clean and smudge decision table

| Action | Input condition | Behavior |
|---|---|---|
| clean | `P` empty | emit empty bytes; no crypto |
| clean | starts with `TCRYPT3:` | fail without stdout; cannot downgrade |
| clean | starts with ASCII `U2FsdGVk` | legacy pass-through, unchanged bytes |
| clean | other nonempty input | derive salt, encrypt, emit canonical v2 object |
| smudge / textconv | starts with `TCRYPT3:` | fail without stdout |
| smudge / textconv | structurally valid v2 blob | attempt legacy decrypt; emit buffered plaintext only on successful OpenSSL completion |
| smudge / textconv | not v2 / bad padding / decrypt failed | pass through original bytes |

**Known legacy hazards:** The marker-only clean pass-through can commit
plaintext deliberately beginning with `U2FsdGVk`. An unauthenticated v2 blob
can also decrypt to altered bytes without a reliable error. These behaviors
cannot be advertised as safe for a modern protocol. Stage hooks and Git
filters are additionally bypassable locally. The modern format must use an
authenticated discriminator, strict validation, and failure-closed
semantics, with *no fallback* to v2 when secure metadata is present.

`smudge` and `textconv` must not emit partial plaintext before detecting a
late OpenSSL error. The amended Bash implementation buffers the output in a
`mktemp`-created 0600 file and unlinks it on exit. The Rust adapter buffers
in memory; both release plaintext only after the adapter reports success.
This is a correctness guarantee about output, not a secure-erasure claim.

## 4. Public, fixed regression vectors

The following tests are canonical examples from the released Bash suite;
passwords are intentionally PUBLIC test strings. Each plaintext includes LF.

| Context | Path | Password | Expected stored bytes without final LF |
|---|---|---|---|
| default | `sensitive_file` | `abc 123` | `U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwbgVd48WaQXznsg42nXbQrlWsf/qiCg` |
| super-secret | `super_sensitive_file` | `321cba` | `U2FsdGVkX1+dAkIV/LAKXMmqjDNOGoOVK8Rmhw9tUnbR4dwBDglpkXIT3yzYBvoc` |

Plaintext for both: ASCII `My secret content\n`. Also test binary bytes,
non-UTF8 filenames on Unix, CRLF Base64 input, deterministic repeats, an
empty protected file, huge files (subprocess pipe backpressure), and
malformed ciphertext. No new v3 implementation may silently reuse `Salted__`.

## 5. Observable error and OS boundaries

A filter that cannot start `openssl` / cannot read local credentials must
report an error and emit no ciphertext. Legacy v2 *decryption failure* is a
specific compatibility exception: it returns the original stored bytes.

The legacy HMAC command sends `F || ':' || W` through `openssl dgst -hmac`
**process argv**, and OpenSSL enc receives `W` through child environment.
Those are **not acceptable for the planned secure v3 implementation**. Rust
and Bash intentionally agree on v2; no formal proof over this byte protocol
would remove process-credential exposure or the MD5/authentication defects.

## 6. Correspondence ledger (review required, not signed off)

| Contract | Bash (`transcrypt`) | Rust actual source | Evidence |
|---|---|---|---|
| v2 magic and early returns | `git_clean`, `git_smudge`, `git_textconv` | `transcrypt-legacy-core::{legacy_looks_encrypted,prohibited_provisional_v3}`; `transcrypt-legacy::{clean,smudge,textconv}` | `tests/interop/check-bash-legacy-contract.sh`, `filter_parity.rs` |
| context and config | `derive_context_config_group`, `load_password` | `transcrypt-legacy-core::valid_context_name`, `transcrypt-legacy::load_settings` | Rust context tests, named-context vectors |
| HMAC key/salt | `git_clean`, OpenSSL `dgst -hmac` | `transcrypt-legacy-core::{legacy_hmac_key,legacy_salt_from_digest}`, `transcrypt-legacy::hmac_sha256` | public golden bytes; Rust/Bash clean comparison |
| envelope bytes | `git_clean`, `hex_to_bin`, `openssl base64` | `transcrypt-protocol::{V2Record,encode_v2,parse_v2}` | v2 fixture vectors, Git staging integration |
| plaintext on decrypt error | `git_smudge`, `git_textconv` | `transcrypt-legacy::{smudge,textconv}` | corrupt ciphertext, zero partial output check |

These are **candidate correspondence links**, not a completed hand audit:
the reviewer must examine every script/command with the checklist in
`docs/verification/09-bash-traceability-and-review.md`, including Git and OS
assumptions. Source changes invalidate that review.

## 7. Boundaries for future Lean/Aeneas refinement

The independent Lean spec should define byte concatenation and slicing,
context validation, ciphertext grammar, and clean/smudge decision cases.
The first Charon/Aeneas target is the **actual** `transcrypt-legacy-core`
crate; later target the real parser in `transcrypt-protocol`. The effectful
Rust CLI/OpenSSL/Git adapter has explicit external contracts; do not claim
it verified merely because the pure kernels are proved.

The modern authenticated crypto algorithm and final public metadata remain
unfrozen per `docs/verification/10-decisions-and-blockers.md`. No v3
ciphertext should be emitted until those decisions are reviewed.
