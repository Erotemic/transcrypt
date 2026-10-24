# 02. Canonical protocol specification: scope and freeze criteria

**Status: prospective, NOT frozen.** The existing `TCRYPT3:` envelope in the
October 2026 Bash prototype is an experimental, incompatible-or-malleable
reference. The released format must not inherit its weaknesses without a
reviewed justification. Any claim of byte-level interoperability refers to
an *explicitly named format revision* and exact approved test vectors.

## 1. Normative layers and their authority

The protocol specification must ultimately be a **complete independent
normative text** with no normative link to implementation source code. Its
components are:

1. **Data representation**: bytes, exact grammar, canonical encoding,
   version/suite discriminator, metadata schema and limits.
2. **Cryptography**: chosen published authenticated deterministic encryption
   scheme, password derivation and salt, keys, associated data, and test
   vectors. Every input transcript must have unambiguous length encoding.
3. **Pure behavior**: deterministic `seal`, strict `open`, classification,
   validation, format selection, errors, context mapping.
4. **Git operational semantics**: state transitions specified in [03](03-git-state-machine.md),
   especially committed vs staged metadata and failure rollback.
5. **Compatibility**: recognized legacy formats and exact fail-closed rules.

Sections 2-6 below are binding *design constraints* but their still-open
cryptographic parameters do not constitute a final byte format. The
[decision register](10-decisions-and-blockers.md) lists exact freeze blockers.

## 2. Input objects and canonicalization

The normative spec will define these distinct byte-oriented types:

| Type | Required definition |
|---|---|
| `Password` | Raw byte sequence acquired through an approved credential channel; Bash supported input subset must be precisely declared. No implicit Unicode normalization. |
| `Context` | Named access domain: ASCII `default` or defined lowercase-hyphenated identifiers; syntactic and length bounds. |
| `PublicConfig` | Parsed canonical in-repository non-secret metadata (cipher suite, KDF, iterations, public salt, version, auth policy, future extension policy). |
| `PrivateConfig` | Local, uncommitted key acquisition and permission policy; never inherited from remote repository. |
| `Path` | Git path as uninterpreted bytes with NUL excluded; display encoding is not identity. |
| `Plaintext` | Arbitrary bytes, including empty, invalid UTF-8, and NUL-containing files. |
| `CiphertextRecord` | Canonical envelope with uniquely interpreted suite/version/fields and authenticated content. |
| `Operation` | `clean`, `smudge`, `textconv`, `init`, `unlock`, `rekey`, `migrate`, `verify-stage`, `flush`. |

The specification must define canonical UTF-8/ASCII and length encoding only
where text exists. Never split Git filenames on whitespace/newlines. Reject
ambiguous config duplicates, unknown mandatory keys, invalid hex/base64,
noncanonical versions, integer overflow, and missing required values.
**No in-band shell source evaluation** occurs when reading public metadata.

## 3. Public configuration

Proposal for a strict, minimal committed file using Git-config-like syntax:

```ini
[transcrypt]
format = secure-v3
suite = <frozen-suite-identifier>
kdf = pbkdf2-hmac-sha256
iterations = <frozen-safe-default-or-explicit-decimal>
base-salt = <lowercase-hex-encoding-of-16-or-more-public-random-bytes>
auth = <frozen-authentication-scheme>
```

**The angle-bracket fields above are NOT valid implementation inputs.** They
mark required protocol-freeze decisions rather than placeholders to paste into
actual Git configuration. At freeze, publish a template containing real
approved values, a complete field-by-field grammar, bounds and a fixture.

Mandatory constraints now:

- Committed public config contains no passwords/derived keys. A fresh
  repository gets a cryptographically generated, password-independent salt.
- New-format `clean`/`smudge` never infer defaults for missing required
  committed fields; missing or malformed config is a hard failure.
- Different contexts are cryptographically separated by explicitly encoded
  domain labels; context association must be unambiguous after clone.
- KDF work factor is explicit in the committed config. Limit minimum,
  maximum, integer representation and resource use *before* executing KDF.
- Salt and crypto parameter changes require a transaction that rewrites all
  ciphertext whose derived keys or authenticating transcript would change.
- The complete authenticated-data binding for a blob must include the
  necessary protocol version, suite identifier, and unambiguous context and
  crypto-configuration commitment. If path-binding is selected, its
  semantics across rename and merge must be defined at freeze.

A configuration digest embedded in each envelope can detect mismatch but
cannot reconstruct a missing config. The pre-commit staged-tree invariant
from [03](03-git-state-machine.md) remains mandatory.

## 4. Cryptographic decision gate (not deferred to implementation)

### Required primitives

- Initial portable KDF baseline: **PBKDF2-HMAC-SHA256**, with an explicit
  work factor and a public salt carrying at least 128 bits from a CSPRNG.
  Exact per-context KDF transcript and key lengths must be frozen and
  covered by known-answer tests. Argon2id is an extension candidate, not
  part of initial compatibility.
- Domain separation must be mechanical and versioned. Prefer a specified
  standardized KDF/expander (e.g., HKDF when appropriate), not ad-hoc string
  concatenations without lengths. If the construction uses direct
  PBKDF2-derived keys for different purposes, explicitly state security
  assumptions and domain labels.
- The encryption scheme must be **authenticated deterministic encryption**
  with verification-before-release. Standardized RFC 5297 AES-SIV is the
  preferred candidate for review, *not an already approved choice*.
- Before selecting AES-SIV, demonstrate that **both** the Rust implementation
  and zero-additional-dependency Bash/OpenSSL implementation can calculate
  identical standardized vectors on the supported toolchain matrix. OpenSSL
  `enc` does not itself provide generic authenticated GCM/CCM modes; do not
  assume it exposes AES-SIV portably through `enc`.
- If portable Bash AES-SIV is not feasible, evaluate a rigorously reviewed
  alternative based on available primitives, documenting its exact security
  proof/assumptions. A bespoke CBC + synthetic-IV + HMAC recipe is not
  accepted just because it passes functional tests. If neither solution
  works with the fixed dependency policy, reconsider the supported v3
  platform matrix or negotiate the constraint with the maintainer **before**
  shipping—not by giving the Bash tool weaker ciphertext silently.

### Determinism and authentication

`seal(K, Context, PublicConfig, Plaintext) -> CiphertextRecord` must be
fully deterministic after the repo's public salt and suite are fixed.
`open(...) -> Plaintext | Failure` verifies the complete authenticated record
and its associated data before any bytes become externally visible.

**Empty plaintext must be handled explicitly**. The proposed secure profile
makes it an authenticated ciphertext record too, not a bare empty blob.
This differs from the October candidate's empty-file pass-through and must
be tested. A zero-length unencrypted blob is not silently accepted as valid
ciphertext in a protected path.

### Representation and versioning

The final spec must include:

- magic/discriminator values distinct from experimental incompatible formats;
  package major version and blob-format version are independent numbers;
- an ABNF-like grammar **and** a precise binary layout, if applicable;
- ASCII/UTF-8 requirements, canonical hex/base64 or raw-byte encoding;
- length encodings, integer endianness and field order;
- max/min lengths and resource bounds, including huge/overflowing fields;
- authenticated transcript covering format/suite/config/context and blob;
- exact handling of CRLF, trailing newline, prefix, whitespace, and padding;
- definitions for strict parser errors and all invalid cases;
- complete standards-derived and independently computed test vectors.

No parser may accept two different encoded strings as the same canonical
record. No valid record from one version may be silently reinterpreted as
another version. Unsupported format/suite is an error.

## 5. Compatibility policy

| Input repository state | Expected default |
|---|---|
| New repo with no prior encryption (even if Git already has normal commits) | Initialize approved secure format once available |
| Existing legacy repo with ciphertext and no secure config | Preserve legacy; prompt for *explicit* migration, never auto-rekey |
| Existing secure repo with complete metadata | Use exactly recorded suite/format; no silent defaults |
| Missing secure metadata with recognizable secure ciphertext | Fail closed; never assume legacy or regenerate salt |
| Unknown/newer envelope in old binary | Fail closed with upgrade instruction |
| Mixed secure and legacy protected blobs outside an explicit transition | Reject or require a documented mixed-version migration state |
| Empty protected file | Canonical authenticated empty record (proposed) |

Legacy reads remain available where the legacy profile applies. Legacy code
is isolated from the secure-format decoder. `clean`, `smudge`, `textconv`,
merge, and staging semantics must be specified for each supported version.
Do not perform an accidental downgrade because a password was wrong or a
modern crypto feature was unavailable.

## 6. Required spec deliverable before writing the final encryption code

A document named `PROTOCOL-<frozen-format-id>.md` must be created at the
freeze stage, with literal algorithms and values (not placeholders), exact
byte-level vectors and expected errors. It must include:

- A closed grammar and suite/parameter registry with one active suite;
- `derive`, `seal`, `open`, `detect_version`, `check_config`, and
  `check_stage` pseudocode without implementation-specific behavior;
- authentication transcript, exact byte lengths and accepted ranges;
- success/failure semantics, including no release of plaintext on failure;
- CLI/context compatibility table and Git state links;
- documented deterministic equality/length leakage;
- references to the approved published cryptographic construction;
- independent Bash and Rust review approvals.

The **current candidate's** exact envelope description belongs in
[reference/current-candidate.md](reference/current-candidate.md), not in the
future normative file.
