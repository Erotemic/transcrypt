#![no_std]
//! Pure, dependency-free Transcrypt v3 wire grammar and protocol decisions.
//! Crypto, Git and filesystem I/O live in the adapter (`transcrypt-v3`).
//! No legacy format recognition, format guessing, or plaintext fallback.
//!
//! The whole crate is translated by Charon/Aeneas and proved in Lean
//! (`proofs/aeneas/v3`). It is written in the subset that translates to
//! readable, provable code:
//!
//! - loops are `while` loops over an explicit index, never iterators or
//!   closures;
//! - no early `return` from inside a nested loop (a single loop may return);
//! - no `?` operator: errors are matched and returned explicitly;
//! - record lengths are literal constants (see `CONFIG_LEN`).
//!
//! Proofs name the generated loops (`*_loop0`, `*_loop1`, ...) by their order
//! inside each function, so reordering loops renames them.

/// Version marker of the committed public configuration.
pub const CONFIG_MAGIC: [u8; 7] = *b"TCFG3\0\x01";
/// Version marker that starts every encrypted file record.
pub const FILE_MAGIC: [u8; 6] = *b"TV3F\0\x01";
/// Length of the public Argon2id salt.
pub const SALT_LEN: usize = 32;
/// Length of an AES-SIV synthetic IV (the authentication tag).
pub const TAG_LEN: usize = 16;
/// Length of the keyless configuration identifier in a file header.
pub const ID_LEN: usize = 16;
// The three record lengths below are written as literals on purpose: a
// literal constant translates to a plain Lean value, whereas a computed one
// (like `FILE_MIN_LEN`) becomes an overflow-checked computation every proof
// must step through. The test `literal_lengths_are_the_field_sums` checks
// the sums.
/// Authenticated part of the configuration: magic and salt (39 = 7 + 32).
pub const CONFIG_PREFIX_LEN: usize = 39;
/// Complete configuration: prefix and tag (55 = 39 + 16).
pub const CONFIG_LEN: usize = 55;
/// File header: magic and configuration identifier (22 = 6 + 16).
pub const FILE_HEADER_LEN: usize = 22;
/// Shortest file record: the header and the tag of an empty plaintext.
pub const FILE_MIN_LEN: usize = FILE_HEADER_LEN + TAG_LEN;

/// Why a fixed-format record was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormatError {
    Length,
    Magic,
}

/// All fields in the public configuration. `tag` is authenticated by the crypto adapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    pub salt: [u8; SALT_LEN],
    pub tag: [u8; TAG_LEN],
}

pub fn encode_config_prefix(salt: &[u8; SALT_LEN]) -> [u8; CONFIG_PREFIX_LEN] {
    let mut out = [0u8; CONFIG_PREFIX_LEN];
    let mut i = 0;
    while i < CONFIG_MAGIC.len() {
        out[i] = CONFIG_MAGIC[i];
        i += 1;
    }
    let mut j = 0;
    while j < SALT_LEN {
        out[CONFIG_MAGIC.len() + j] = salt[j];
        j += 1;
    }
    out
}

pub fn encode_config(config: &Config) -> [u8; CONFIG_LEN] {
    let mut out = [0u8; CONFIG_LEN];
    let prefix = encode_config_prefix(&config.salt);
    let mut i = 0;
    while i < CONFIG_PREFIX_LEN {
        out[i] = prefix[i];
        i += 1;
    }
    let mut j = 0;
    while j < TAG_LEN {
        out[CONFIG_PREFIX_LEN + j] = config.tag[j];
        j += 1;
    }
    out
}

/// Decode the fixed-size committed config record: check the magic and split
/// out salt and tag. Authentication is a separate step
/// (`authenticate_config`) performed *after* this structural parse.
pub fn decode_config_exact(input: &[u8; CONFIG_LEN]) -> Result<Config, FormatError> {
    if !matches_at(input, 0, &CONFIG_MAGIC) {
        return Err(FormatError::Magic);
    }
    let mut salt = [0u8; SALT_LEN];
    let mut j = 0;
    while j < SALT_LEN {
        salt[j] = input[CONFIG_MAGIC.len() + j];
        j += 1;
    }
    let mut tag = [0u8; TAG_LEN];
    let mut k = 0;
    while k < TAG_LEN {
        tag[k] = input[CONFIG_PREFIX_LEN + k];
        k += 1;
    }
    Ok(Config { salt, tag })
}

/// Reject unknown versions, truncated/extended metadata and malformed magic.
/// This public slice boundary checks the length and delegates the content
/// decision to `decode_config_exact`.
pub fn parse_config(input: &[u8]) -> Result<Config, FormatError> {
    if input.len() != CONFIG_LEN {
        return Err(FormatError::Length);
    }
    let mut record = [0u8; CONFIG_LEN];
    let mut i = 0;
    while i < CONFIG_LEN {
        record[i] = input[i];
        i += 1;
    }
    decode_config_exact(&record)
}

pub fn encode_file_header(id: &[u8; ID_LEN]) -> [u8; FILE_HEADER_LEN] {
    let mut out = [0u8; FILE_HEADER_LEN];
    let mut i = 0;
    while i < FILE_MAGIC.len() {
        out[i] = FILE_MAGIC[i];
        i += 1;
    }
    let mut j = 0;
    while j < ID_LEN {
        out[FILE_MAGIC.len() + j] = id[j];
        j += 1;
    }
    out
}

/// Decode a fixed-width file header: check the magic and return the
/// configuration identifier. `parse_file_header` additionally checks that at
/// least `TAG_LEN` body bytes follow; authenticating the complete record is
/// the caller's job.
pub fn decode_file_header_exact(input: &[u8; FILE_HEADER_LEN]) -> Result<[u8; ID_LEN], FormatError> {
    if !matches_at(input, 0, &FILE_MAGIC) {
        return Err(FormatError::Magic);
    }
    let mut id = [0u8; ID_LEN];
    let mut j = 0;
    while j < ID_LEN {
        id[j] = input[FILE_MAGIC.len() + j];
        j += 1;
    }
    Ok(id)
}

/// Parses only the public envelope header; authenticity is *not* established here.
/// Callers must authenticate the complete message before releasing plaintext.
pub fn parse_file_header(input: &[u8]) -> Result<[u8; ID_LEN], FormatError> {
    if input.len() < FILE_MIN_LEN {
        return Err(FormatError::Length);
    }
    let mut header = [0u8; FILE_HEADER_LEN];
    let mut i = 0;
    while i < FILE_HEADER_LEN {
        header[i] = input[i];
        i += 1;
    }
    decode_file_header_exact(&header)
}

// ---------------------------------------------------------------------------
// Protocol decision core.
//
// The effectful adapter (`transcrypt-v3`) supplies cryptographic primitives
// through `V3Primitives` and performs Git/filesystem I/O; every *decision*
// about whether bytes may be sealed, released, published or flushed is made
// here, so the adapter cannot skip a gate.
// ---------------------------------------------------------------------------

/// Largest plaintext accepted by any v3 operation (16 MiB).
pub const MAX_FILE: usize = 16 * 1024 * 1024;
/// Largest canonical Git-relative pathname accepted as associated data.
pub const MAX_PATH: usize = 4096;
/// Largest record or agent body: a maximal plaintext plus its envelope.
pub const MAX_RECORD: usize = MAX_FILE + FILE_MIN_LEN;
/// The Git attribute that selects protected files.
pub const FILTER_ATTR: [u8; 6] = *b"filter";
/// The value of `FILTER_ATTR` that protects a file.
pub const FILTER_DRIVER: [u8; 13] = *b"transcrypt-v3";
// Repository metadata that Git or v3 must read unencrypted
// (`is_reserved_path`).
/// The committed configuration directory (a path prefix).
pub const METADATA_DIR: [u8; 12] = *b".transcrypt/";
/// The top-level attribute file.
pub const ATTRIBUTES_NAME: [u8; 14] = *b".gitattributes";
/// An attribute file in any subdirectory (a path suffix).
pub const ATTRIBUTES_SUFFIX: [u8; 15] = *b"/.gitattributes";
/// The submodule map.
pub const MODULES_NAME: [u8; 11] = *b".gitmodules";
/// The committed public configuration (in `METADATA_DIR`).
pub const CONFIG_PATH: [u8; 18] = *b".transcrypt/config";

/// Every reason the protocol core refuses an operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// Path is not a canonical Git-relative pathname that may be protected.
    Path,
    /// Input, output buffer or record exceeds or mismatches a size bound.
    Size,
    /// Public configuration is structurally malformed.
    Config,
    /// Configuration tag did not verify: wrong passphrase or tampering.
    ConfigAuthentication,
    /// Record envelope is malformed.
    Envelope,
    /// Record belongs to a different public configuration.
    ConfigMismatch,
    /// Record failed AES-SIV authentication under this config and path.
    Authentication,
    /// Clean input already is a v3 record; refuse double encryption.
    DoubleEncryption,
    /// The sealing primitive reported failure.
    Primitive,
    /// A worktree file is neither the staged record nor its plaintext.
    UnexpectedWorktree,
    /// Agent request is malformed or not permitted.
    Request,
    /// A `git ls-files --stage -z` record is malformed or not stage 0.
    Index,
    /// A `git check-attr -z` record is malformed or names another path.
    Attribute,
    /// A record of another configuration, or bytes that are no v3 record,
    /// where a record of this configuration is required.
    Foreign,
}

/// The cryptographic boundary. Implementations must realize exactly the
/// primitives of `docs/verification/specs/V3-AUTHENTICATED-P0.md`:
/// deterministic RFC 5297 AES-256-CMAC-SIV under one derived key, and a
/// keyless SHA-256 truncation. Their correctness and security are trusted
/// assumptions; the Lean development states them as an explicit contract.
pub trait V3Primitives {
    /// Write `AES-SIV(K).encrypt("", [CONFIG_DOMAIN, prefix])`, i.e. the
    /// 16-byte tag, into `tag`.
    fn seal_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &mut [u8; TAG_LEN]) -> bool;
    /// Verify `tag` as the AES-SIV encryption of the empty plaintext under
    /// `[CONFIG_DOMAIN, prefix]`.
    fn open_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &[u8; TAG_LEN]) -> bool;
    /// Write `AES-SIV(K).encrypt(plaintext, [FILE_DOMAIN, config, path])`
    /// (tag then ciphertext) into `out`, whose length is `plaintext.len() + TAG_LEN`.
    fn seal_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], plaintext: &[u8], out: &mut [u8]) -> bool;
    /// Authenticate and decrypt `sealed` under `[FILE_DOMAIN, config, path]`
    /// into `out`, whose length is `sealed.len() - TAG_LEN`. Returns false,
    /// and must not be trusted to leave `out` meaningful, on failure.
    fn open_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], sealed: &[u8], out: &mut [u8]) -> bool;
    /// `SHA-256(config)[0..16]`; keyless public discriminator.
    fn config_id(&self, config: &[u8; CONFIG_LEN]) -> [u8; ID_LEN];
}

/// Byte-string equality by explicit comparison of every position.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether `bytes[at..]` starts with `expected`.
fn matches_at(bytes: &[u8], at: usize, expected: &[u8]) -> bool {
    if at > bytes.len() || bytes.len() - at < expected.len() {
        return false;
    }
    let mut k = 0;
    while k < expected.len() {
        if bytes[at + k] != expected[k] {
            return false;
        }
        k += 1;
    }
    true
}

/// The position of the first `byte` in `bytes[from..]`, or `bytes.len()` if
/// there is none (`from` itself when it is past the end).
fn find_byte(bytes: &[u8], from: usize, byte: u8) -> usize {
    let mut j = from;
    while j < bytes.len() && bytes[j] != byte {
        j += 1;
    }
    j
}

/// Whether `bytes` ends with `suffix`.
fn ends_with(bytes: &[u8], suffix: &[u8]) -> bool {
    bytes.len() >= suffix.len() && matches_at(bytes, bytes.len() - suffix.len(), suffix)
}

/// Whether `path` is an attribute file: the top-level `.gitattributes` or
/// one in any subdirectory.
pub fn is_attributes_path(path: &[u8]) -> bool {
    bytes_eq(path, &ATTRIBUTES_NAME) || ends_with(path, &ATTRIBUTES_SUFFIX)
}

/// Paths that are never protected, whatever the attributes say: anything in
/// `.transcrypt/` (the public configuration), every `.gitattributes` (Git
/// reads the staged blob to decide what is protected) and `.gitmodules`.
/// Which other paths are protected is the user's choice, made with Git
/// attributes (`filter=transcrypt-v3`); see `parse_attr_record`.
pub fn is_reserved_path(path: &[u8]) -> bool {
    matches_at(path, 0, &METADATA_DIR) || is_attributes_path(path) || bytes_eq(path, &MODULES_NAME)
}

/// Whether `path` is committed protection policy: an attribute file (which
/// paths are protected) or the public configuration (under which key).
pub fn is_policy_path(path: &[u8]) -> bool {
    is_attributes_path(path) || bytes_eq(path, &CONFIG_PATH)
}

/// A path component `path[start..end]` is acceptable iff it is nonempty and
/// neither `.` nor `..`.
fn component_ok(path: &[u8], start: usize, end: usize) -> bool {
    let len = end - start;
    if len == 0 {
        return false;
    }
    if len == 1 && path[start] == b'.' {
        return false;
    }
    !(len == 2 && path[start] == b'.' && path[start + 1] == b'.')
}

/// The authenticated-path policy: nonempty, at most `MAX_PATH` bytes, no NUL,
/// every `/`-separated component nonempty and neither `.` nor `..` (so no
/// absolute paths, duplicate or trailing separators), and not reserved
/// metadata. Raw bytes are authoritative; there is no Unicode or filesystem
/// normalization. Any such path may be protected.
pub fn is_canonical_protected_path(path: &[u8]) -> bool {
    let n = path.len();
    if n == 0 || n > MAX_PATH {
        return false;
    }
    let mut ok = true;
    let mut start = 0;
    let mut i = 0;
    while ok && i <= n {
        if i == n || path[i] == b'/' {
            ok = component_ok(path, start, i);
            start = i + 1;
        } else if path[i] == b'\0' {
            ok = false;
        }
        i += 1;
    }
    ok && !is_reserved_path(path)
}

/// Create the public configuration for a freshly derived key and salt.
pub fn initialize_config<P: V3Primitives>(primitives: &P, salt: &[u8; SALT_LEN]) -> Result<[u8; CONFIG_LEN], Refusal> {
    let prefix = encode_config_prefix(salt);
    let mut tag = [0u8; TAG_LEN];
    if !primitives.seal_config(&prefix, &mut tag) {
        return Err(Refusal::Primitive);
    }
    Ok(encode_config(&Config { salt: *salt, tag }))
}

/// Parse and authenticate the public configuration under the held key.
pub fn authenticate_config<P: V3Primitives>(primitives: &P, config: &[u8; CONFIG_LEN]) -> Result<Config, Refusal> {
    let parsed = match decode_config_exact(config) {
        Ok(parsed) => parsed,
        Err(_) => return Err(Refusal::Config),
    };
    let prefix = encode_config_prefix(&parsed.salt);
    if !primitives.open_config(&prefix, &parsed.tag) {
        return Err(Refusal::ConfigAuthentication);
    }
    Ok(parsed)
}

/// The clean direction. On success `out` holds the complete record
/// `header(config_id(config)) || seal_file(config, path, plaintext)`.
/// `out.len()` must equal `plaintext.len() + FILE_MIN_LEN`.
pub fn seal_record<P: V3Primitives>(
    primitives: &P,
    config: &[u8; CONFIG_LEN],
    path: &[u8],
    plaintext: &[u8],
    out: &mut [u8],
) -> Result<(), Refusal> {
    if plaintext.len() > MAX_FILE || out.len() != plaintext.len() + FILE_MIN_LEN {
        return Err(Refusal::Size);
    }
    if !is_canonical_protected_path(path) {
        return Err(Refusal::Path);
    }
    if let Err(refusal) = authenticate_config(primitives, config) {
        return Err(refusal);
    }
    if parse_file_header(plaintext).is_ok() {
        return Err(Refusal::DoubleEncryption);
    }
    let header = encode_file_header(&primitives.config_id(config));
    let mut i = 0;
    while i < FILE_HEADER_LEN {
        out[i] = header[i];
        i += 1;
    }
    if !primitives.seal_file(config, path, plaintext, &mut out[FILE_HEADER_LEN..]) {
        return Err(Refusal::Primitive);
    }
    Ok(())
}

/// The smudge/verify direction. Plaintext is written to `out` and success
/// reported only after the path, configuration, envelope, configuration
/// identifier and AES-SIV authentication all succeed. If authentication
/// fails, `out` is zeroed.
/// `out.len()` must equal `record.len() - FILE_MIN_LEN`.
pub fn open_record<P: V3Primitives>(
    primitives: &P,
    config: &[u8; CONFIG_LEN],
    path: &[u8],
    record: &[u8],
    out: &mut [u8],
) -> Result<(), Refusal> {
    if record.len() > MAX_RECORD {
        return Err(Refusal::Size);
    }
    if !is_canonical_protected_path(path) {
        return Err(Refusal::Path);
    }
    if let Err(refusal) = authenticate_config(primitives, config) {
        return Err(refusal);
    }
    let id = match parse_file_header(record) {
        Ok(id) => id,
        Err(_) => return Err(Refusal::Envelope),
    };
    // `parse_file_header` succeeded, so `record.len() >= FILE_MIN_LEN`.
    if record.len() - FILE_MIN_LEN != out.len() {
        return Err(Refusal::Size);
    }
    if !bytes_eq(&id, &primitives.config_id(config)) {
        return Err(Refusal::ConfigMismatch);
    }
    if !primitives.open_file(config, path, &record[FILE_HEADER_LEN..], out) {
        // Never leave unauthenticated primitive output in the caller's buffer.
        let mut i = 0;
        while i < out.len() {
            out[i] = 0;
            i += 1;
        }
        return Err(Refusal::Authentication);
    }
    Ok(())
}

/// Hydration of one protected file whose staged record has already been
/// opened to `plaintext`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HydrateAction {
    /// The worktree holds exactly the staged record: replace it by plaintext.
    Publish,
    /// The worktree already holds exactly the authenticated plaintext.
    Keep,
}

/// Never overwrite bytes that are neither the staged ciphertext nor its
/// authenticated plaintext: those may be the user's only copy of new data.
pub fn hydrate_action(worktree: &[u8], record: &[u8], plaintext: &[u8]) -> Result<HydrateAction, Refusal> {
    if bytes_eq(worktree, record) {
        return Ok(HydrateAction::Publish);
    }
    if bytes_eq(worktree, plaintext) {
        return Ok(HydrateAction::Keep);
    }
    Err(Refusal::UnexpectedWorktree)
}

/// Locking of one protected file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LockAction {
    /// The worktree already holds exactly the staged record.
    Keep,
    /// The worktree plaintext seals to exactly the staged record: replace it.
    Flush,
}

/// Decide whether the worktree may be replaced by the staged record.
/// `resealed` is `seal_record` applied to the worktree bytes (performed by the
/// credential agent, which alone holds the key); it is ignored when the
/// worktree already is the record. A plaintext is only discarded when
/// sealing it reproduces the staged record byte for byte, so `lock` never
/// destroys uncommitted plaintext.
pub fn lock_action(worktree: &[u8], record: &[u8], resealed: &[u8]) -> Result<LockAction, Refusal> {
    if bytes_eq(worktree, record) {
        return Ok(LockAction::Keep);
    }
    if bytes_eq(resealed, record) {
        return Ok(LockAction::Flush);
    }
    Err(Refusal::UnexpectedWorktree)
}

/// Requests understood by the credential agent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgentOp {
    Ping,
    Encrypt,
    Decrypt,
    Stop,
}

/// Authorize one framed agent request against the configuration the agent
/// authenticated at startup. Data operations require a canonical protected
/// path; control operations carry no path or body.
pub fn authorize_agent_request(
    opcode: u8,
    supplied: &[u8; CONFIG_LEN],
    active: &[u8; CONFIG_LEN],
    path: &[u8],
    body_len: usize,
) -> Result<AgentOp, Refusal> {
    if path.len() > MAX_PATH || body_len > MAX_RECORD {
        return Err(Refusal::Size);
    }
    if !bytes_eq(supplied, active) {
        return Err(Refusal::ConfigMismatch);
    }
    if opcode == b'E' || opcode == b'D' {
        if !is_canonical_protected_path(path) {
            return Err(Refusal::Path);
        }
        if opcode == b'E' {
            return Ok(AgentOp::Encrypt);
        }
        return Ok(AgentOp::Decrypt);
    }
    if path.len() != 0 || body_len != 0 {
        return Err(Refusal::Request);
    }
    if opcode == b'P' {
        return Ok(AgentOp::Ping);
    }
    if opcode == b'X' {
        return Ok(AgentOp::Stop);
    }
    Err(Refusal::Request)
}

/// One record of `git check-attr -z filter` output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AttrRecord {
    /// The value is exactly `transcrypt-v3`: the path is protected.
    pub protected: bool,
    /// Where the next record starts.
    pub next: usize,
}

/// Parse the record at `response[start..]`, which must be
/// `path NUL filter NUL value NUL` for exactly the requested `path` (Git
/// answers `--stdin` requests in order). `value` is `unspecified`, `set`,
/// `unset` or a driver name; only `transcrypt-v3` protects. Selection is
/// Git's own attribute evaluation: v3 never matches patterns itself.
pub fn parse_attr_record(response: &[u8], start: usize, path: &[u8]) -> Result<AttrRecord, Refusal> {
    let n = response.len();
    // Room for `path NUL filter NUL NUL` at least, written without any
    // addition that could overflow.
    if start > n || n - start < path.len() || n - start - path.len() < FILTER_ATTR.len() + 3 {
        return Err(Refusal::Attribute);
    }
    let name = start + path.len();
    if !matches_at(response, start, path)
        || response[name] != b'\0'
        || !matches_at(response, name + 1, &FILTER_ATTR)
        || response[name + 1 + FILTER_ATTR.len()] != b'\0'
    {
        return Err(Refusal::Attribute);
    }
    let value = name + FILTER_ATTR.len() + 2;
    let end = find_byte(response, value, b'\0');
    if end == n {
        return Err(Refusal::Attribute);
    }
    Ok(AttrRecord { protected: bytes_eq(&response[value..end], &FILTER_DRIVER), next: end + 1 })
}

/// Parse Git's complete answer to a `check-attr -z --stdin filter` request:
/// `request` is the exact stdin sent (each path followed by one NUL) and
/// `flags` has one slot per requested path. Succeeds only if `response` is
/// one record per requested path, in order (`parse_attr_record`), and
/// nothing else; then `flags[i]` says whether path `i` is protected. On
/// failure the flags must not be used.
pub fn parse_attr_response(request: &[u8], response: &[u8], flags: &mut [bool]) -> bool {
    let mut ok = true;
    let mut start = 0;
    let mut at = 0;
    let mut i = 0;
    let mut k = 0;
    while ok && k < request.len() {
        if request[k] == b'\0' {
            if i < flags.len() {
                match parse_attr_record(response, at, &request[start..k]) {
                    Ok(record) => {
                        flags[i] = record.protected;
                        at = record.next;
                        i += 1;
                        start = k + 1;
                    }
                    Err(_) => ok = false,
                }
            } else {
                ok = false;
            }
        }
        k += 1;
    }
    ok && start == request.len() && i == flags.len() && at == response.len()
}

/// Length of a big-endian `u32` (`encode_be_u32`).
pub const BE_U32_LEN: usize = 4;
/// Where a request header's config starts: after the one-byte opcode.
pub const FRAME_CONFIG_START: usize = 1;
/// Where a request header's path length starts: after the opcode and the
/// config (56 = 1 + 55).
pub const FRAME_LEN_START: usize = 56;
/// Length of a credential-agent request header: opcode, the 55-byte public
/// config and the big-endian path length. The path and a big-endian body
/// length follow (local IPC only, not part of the committed wire format).
pub const FRAME_HEADER_LEN: usize = FRAME_LEN_START + BE_U32_LEN;

/// Encode an agent request header.
pub fn encode_frame_header(opcode: u8, config: &[u8; CONFIG_LEN], path_len: u32) -> [u8; FRAME_HEADER_LEN] {
    let mut out = [0u8; FRAME_HEADER_LEN];
    out[0] = opcode;
    let mut i = 0;
    while i < CONFIG_LEN {
        out[FRAME_CONFIG_START + i] = config[i];
        i += 1;
    }
    let len = encode_be_u32(path_len);
    let mut k = 0;
    while k < BE_U32_LEN {
        out[FRAME_LEN_START + k] = len[k];
        k += 1;
    }
    out
}

/// Decoded agent request header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameHeader {
    pub opcode: u8,
    pub config: [u8; CONFIG_LEN],
    pub path_len: u32,
}

/// Decode an agent request header (every byte string of this length is a
/// header; authorization is `authorize_agent_request`'s job).
pub fn decode_frame_header(input: &[u8; FRAME_HEADER_LEN]) -> FrameHeader {
    let mut config = [0u8; CONFIG_LEN];
    let mut i = 0;
    while i < CONFIG_LEN {
        config[i] = input[FRAME_CONFIG_START + i];
        i += 1;
    }
    let len = [
        input[FRAME_LEN_START],
        input[FRAME_LEN_START + 1],
        input[FRAME_LEN_START + 2],
        input[FRAME_LEN_START + 3],
    ];
    FrameHeader { opcode: input[0], config, path_len: decode_be_u32(&len) }
}

/// Big-endian `u32` encoding used for agent frame lengths.
pub fn encode_be_u32(x: u32) -> [u8; BE_U32_LEN] {
    [(x >> 24) as u8, (x >> 16) as u8, (x >> 8) as u8, x as u8]
}

/// Inverse of `encode_be_u32`.
pub fn decode_be_u32(b: &[u8; BE_U32_LEN]) -> u32 {
    ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32)
}

/// Length of a Git file mode in an index or tree record.
pub const MODE_LEN: usize = 6;
/// Git modes of a regular file: non-executable and executable.
pub const REGULAR_MODE: [u8; MODE_LEN] = *b"100644";
pub const EXECUTABLE_MODE: [u8; MODE_LEN] = *b"100755";
/// Where an index or tree record's object id starts: after the mode
/// (`MODE_LEN` bytes) and one SP.
pub const OID_START: usize = 7;
/// Length of `OID_END`.
pub const OID_END_LEN: usize = 3;
/// The bytes between an object id and the path in an index record.
const OID_END: [u8; OID_END_LEN] = *b" 0\t";
/// The bytes of an index or tree record besides its object id and path:
/// the mode, SP, and `OID_END` (10 = 7 + 3).
pub const ENTRY_FIXED_LEN: usize = 10;

/// One parsed `git ls-files --stage -z` record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IndexEntry {
    /// The mode is `100644` or `100755`: a file whose content Git filters
    /// (not a symlink, whose target Git stores unfiltered, or a submodule).
    pub regular: bool,
    /// The path is `entry[path_start..]`: everything after the first TAB.
    pub path_start: usize,
}

/// Parse a stage-0 record `<6-byte mode> SP <object id> SP 0 TAB <path>`.
/// The path, which becomes AES-SIV associated data, is everything after the
/// *first* TAB (Git paths may themselves contain TABs; modes and object ids
/// cannot). Unmerged entries (stage 1-3) and malformed records are refused.
/// The object id `entry[OID_START..path_start - OID_END_LEN]` is not inspected here: the
/// adapter checks it with `is_object_id` before passing it to Git.
pub fn parse_index_entry(entry: &[u8]) -> Result<IndexEntry, Refusal> {
    let n = entry.len();
    let t = find_byte(entry, 0, b'\t');
    // `t == n` when there is no TAB.
    if t >= n {
        return Err(Refusal::Index);
    }
    let path_start = t + 1;
    // The object id is the `path_start - ENTRY_FIXED_LEN` bytes between the
    // mode's SP and `OID_END`; it and the path must be nonempty.
    if path_start <= ENTRY_FIXED_LEN
        || path_start == n
        || entry[MODE_LEN] != b' '
        || !matches_at(entry, path_start - OID_END_LEN, &OID_END)
    {
        return Err(Refusal::Index);
    }
    let regular = matches_at(entry, 0, &REGULAR_MODE) || matches_at(entry, 0, &EXECUTABLE_MODE);
    Ok(IndexEntry { regular, path_start })
}

/// Lengths of a SHA-1 and a SHA-256 Git object name in hexadecimal digits.
pub const SHA1_OID_LEN: usize = 40;
pub const SHA256_OID_LEN: usize = 64;

/// A Git object name as printed by `ls-files --stage` or `ls-tree`: 40
/// (SHA-1) or 64 (SHA-256) lowercase hexadecimal digits. The adapter passes
/// only such names to `git cat-file`, never revision syntax such as
/// `:<stage>:<path>` or text that Git could read as an option.
pub fn is_object_id(oid: &[u8]) -> bool {
    let n = oid.len();
    // Non-short-circuit `|`: the translation of a `||` value does not typecheck.
    let mut ok = (n == SHA1_OID_LEN) | (n == SHA256_OID_LEN);
    let mut i = 0;
    while ok && i < n {
        let c = oid[i];
        ok = (c >= b'0' && c <= b'9') || (c >= b'a' && c <= b'f');
        i += 1;
    }
    ok
}

/// Keyless check of a committed record: its size is within bounds, it has
/// the v3 file header, and the header names configuration `id`. Without the
/// key this cannot authenticate, but it rejects every plaintext that is not
/// deliberately formatted as a record for this configuration. This is the
/// check run on pushed history and by server-side audits.
pub fn record_envelope_ok(record: &[u8], id: &[u8; ID_LEN]) -> bool {
    record_envelope_prefix_ok(record.len(), record, id)
}

/// How many leading bytes of a record its keyless envelope depends on: those
/// `parse_file_header` needs (the header, and enough bytes to show the record
/// is not truncated).
pub const ENVELOPE_PREFIX_LEN: usize = FILE_MIN_LEN;

/// `record_envelope_ok` of a record of `size` bytes, decided from its first
/// `ENVELOPE_PREFIX_LEN` bytes `prefix` (any further bytes are ignored), so
/// a reader need not load the rest. The answer holds for any caller: a
/// `size` outside `FILE_MIN_LEN..=MAX_RECORD`, or a `prefix` longer than
/// `size`, is refused whatever the bytes say.
pub fn record_envelope_prefix_ok(size: usize, prefix: &[u8], id: &[u8; ID_LEN]) -> bool {
    if size < FILE_MIN_LEN || size > MAX_RECORD || prefix.len() > size {
        return false;
    }
    // `parse_file_header` refuses prefixes shorter than `FILE_MIN_LEN`, and
    // reads only the first `FILE_HEADER_LEN` bytes.
    match parse_file_header(prefix) {
        Ok(found) => bytes_eq(&found, id),
        Err(_) => false,
    }
}

/// What the smudge filter does with a committed blob at a protected path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmudgeAction {
    /// Authenticate and decrypt it (`open_record`).
    Open,
    /// Leave it encrypted: a record that cannot be opened here (locked, or
    /// another configuration such as history from before a rekey).
    Keep,
}

/// Decide the smudge of `blob` for configuration `id`. Only a v3 record is
/// ever let through unchanged, so a checkout never presents unauthenticated
/// non-record bytes (plaintext that bypassed the filter) as a protected
/// file. A record of this configuration is opened when `unlocked`, and that
/// open authenticates it or fails.
pub fn smudge_action(blob: &[u8], id: &[u8; ID_LEN], unlocked: bool) -> Result<SmudgeAction, Refusal> {
    if blob.len() > MAX_RECORD {
        return Err(Refusal::Size);
    }
    match parse_file_header(blob) {
        Err(_) => Err(Refusal::Foreign),
        Ok(found) => {
            if unlocked && bytes_eq(&found, id) {
                Ok(SmudgeAction::Open)
            } else {
                Ok(SmudgeAction::Keep)
            }
        }
    }
}

/// Where the content of one staged protected entry came from. The
/// pre-commit hook repairs only what the user staged: content that came
/// from a commit is checked, never re-encrypted, so a hostile commit's moved
/// or plaintext content cannot be laundered into a genuine record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Provenance {
    /// From history: `HEAD` holds its blob at its path, or one of the
    /// commits being merged, picked, reverted or rebased does.
    Committed,
    /// The user staged it: neither `HEAD` nor the commits being brought in
    /// (which are known) hold its blob at its path.
    Local,
    /// Not shown to be the user's change, but `protect` selected it: its
    /// plaintext is sealed; a record is left to verification.
    Forced,
    /// Not in `HEAD`, and the commits being brought in are not known (a
    /// rebase or `git am` without a known commit): nothing is repaired.
    Unknown,
}

/// What a staged protected blob is, as the adapter finds it with the key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecordClass {
    /// It opens at the entry's own path (`open_record`).
    OpensHere,
    /// It has no v3 file header (`parse_file_header` refuses it).
    Plaintext,
    /// It has the header, does not open at its own path, and opens at the
    /// path of record `source` of `HEAD`, a place it was moved from
    /// (`next_move_source`).
    MovedFrom(usize),
    /// It has the header but opens neither at its own path nor at any
    /// place it was moved from.
    Unusable,
}

/// Why the pre-commit hook leaves an entry to verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeaveReason {
    /// Not the user's change (or a record that `protect` selected, which it
    /// never re-encrypts): checked, never repaired.
    NotLocal,
    /// The user's record, which opens nowhere it could be re-encrypted from.
    OpensNowhere,
}

/// What the pre-commit hook does with one staged protected entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RepairPlan {
    /// The staged blob already opens at its own path.
    Keep,
    /// Seal the staged blob, which is plaintext, at its path.
    Seal,
    /// Re-seal, for this path, the plaintext of the record as it opens at
    /// the path of record `source` of `HEAD`, which it was moved from.
    Rebind(usize),
    /// Change nothing; verification decides (and refuses a bad record).
    Leave(LeaveReason),
}

/// Whether the hook must read and classify an entry's blob: only for an
/// entry it may repair. Every other entry is `Keep` or `Leave` whatever its
/// blob is, and is verified right after.
pub fn needs_record(provenance: Provenance) -> bool {
    match provenance {
        Provenance::Local => true,
        Provenance::Forced => true,
        Provenance::Committed => false,
        Provenance::Unknown => false,
    }
}

/// The pre-commit repair decision for an entry of `provenance` whose blob is
/// `record`. A blob that opens is kept; only the user's own content is
/// repaired: plaintext is sealed (also when `protect` forced it), and a
/// record the user moved is re-sealed from where it was moved from.
pub fn repair_plan(provenance: Provenance, record: RecordClass) -> RepairPlan {
    match record {
        RecordClass::OpensHere => RepairPlan::Keep,
        RecordClass::Plaintext => match provenance {
            Provenance::Local => RepairPlan::Seal,
            Provenance::Forced => RepairPlan::Seal,
            Provenance::Committed => RepairPlan::Leave(LeaveReason::NotLocal),
            Provenance::Unknown => RepairPlan::Leave(LeaveReason::NotLocal),
        },
        RecordClass::MovedFrom(source) => match provenance {
            Provenance::Local => RepairPlan::Rebind(source),
            Provenance::Forced => RepairPlan::Leave(LeaveReason::NotLocal),
            Provenance::Committed => RepairPlan::Leave(LeaveReason::NotLocal),
            Provenance::Unknown => RepairPlan::Leave(LeaveReason::NotLocal),
        },
        RecordClass::Unusable => match provenance {
            Provenance::Local => RepairPlan::Leave(LeaveReason::OpensNowhere),
            Provenance::Forced => RepairPlan::Leave(LeaveReason::NotLocal),
            Provenance::Committed => RepairPlan::Leave(LeaveReason::NotLocal),
            Provenance::Unknown => RepairPlan::Leave(LeaveReason::NotLocal),
        },
    }
}

/// How the pre-commit hook's final check examines one staged protected entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryCheck {
    /// The blob must open at the entry's path (`open_record`).
    Authenticate,
    /// The blob must have this configuration's envelope
    /// (`record_envelope_ok`). The entry is unchanged since `HEAD` and
    /// `HEAD^1`, so a copy of it is reported where it was made.
    Envelope,
    /// The blob must have the envelope and must not be another path's blob:
    /// a record moved without the key is refused.
    EnvelopeNotMoved,
}

/// The final check of one protected entry. `keyed`: the key is available.
/// `incremental`: the pre-commit hook, which trusts history. `settled`: the
/// entry is unchanged since `HEAD` and `HEAD^1`. With the key every entry
/// authenticates, except a settled one in the incremental hook; otherwise
/// only the envelope is checked, and an unsettled entry must not have been
/// moved.
pub fn entry_check(keyed: bool, incremental: bool, settled: bool) -> EntryCheck {
    if keyed && (!incremental || !settled) {
        EntryCheck::Authenticate
    } else if settled {
        EntryCheck::Envelope
    } else {
        EntryCheck::EnvelopeNotMoved
    }
}

/// How the pre-commit hook's final check examines one index entry, protected
/// or not. With the key, the hook keeps one invariant of every commit it
/// accepts, whatever selects the paths: every regular, non-reserved entry
/// whose blob has this configuration's envelope authenticates at its own
/// path. So, while the configuration is the same, an entry `HEAD` holds
/// needs no authentication (no attribute source can turn a forged record of
/// `HEAD` into a protected file), and every other entry is checked as it
/// enters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StagedCheck {
    /// Nothing to check: a symlink or submodule; reserved metadata `HEAD`
    /// holds; or an unprotected file `HEAD` holds, checked when it entered
    /// (or, without the key, that nothing here could authenticate).
    Skip,
    /// An unprotected file staged since `HEAD`: it must not be a record of
    /// this configuration (`git mv x.env x.bak`), which would be committed
    /// where nothing decrypts it.
    NotRecord,
    /// An unprotected file `HEAD` holds, in a check that does not trust
    /// `HEAD` (a full check, or the policy changed): if it is a record of
    /// this configuration it must authenticate at its path.
    AuthenticateIfRecord,
    /// A protected entry, checked as `entry_check` says.
    Protected(EntryCheck),
}

/// The final check of entry `i` of the index listing (`index`,
/// `index_ends`). `flags`: Git's selection of each entry; `in_head` and
/// `in_parent`: whether `HEAD` and `HEAD^1` hold the entry's blob at its path
/// (`held_entries`; `in_parent` is read only for protected entries);
/// `guard`: the settled guard (`policy_unchanged`); `keyed` and
/// `incremental` as for `entry_check`. A protected entry is settled only when
/// the guard holds and `HEAD` and `HEAD^1` hold it. An unprotected file
/// staged since `HEAD` must not be a record; one that `HEAD` holds is trusted
/// from `HEAD` in the incremental hook under the guard, and otherwise, with
/// the key, authenticated if it is a record.
#[allow(clippy::too_many_arguments)]
pub fn staged_check(
    index: &[u8],
    index_ends: &[usize],
    i: usize,
    flags: &[bool],
    in_head: &[bool],
    in_parent: &[bool],
    keyed: bool,
    incremental: bool,
    guard: bool,
) -> StagedCheck {
    if flags[i] {
        StagedCheck::Protected(entry_check(keyed, incremental, guard & in_head[i] & in_parent[i]))
    } else {
        match listing_fields(index, index_ends, i) {
            Some(f) => {
                if !f.regular {
                    StagedCheck::Skip
                } else if !in_head[i] {
                    StagedCheck::NotRecord
                } else if keyed && (!incremental || !guard) && !is_reserved_path(&index[f.path_start..f.end]) {
                    StagedCheck::AuthenticateIfRecord
                } else {
                    StagedCheck::Skip
                }
            }
            None => StagedCheck::Skip,
        }
    }
}

/// Whether the check reads the entry's whole blob (the `record` of
/// `staged_verdict`): only a protected entry's.
pub fn reads_blob(check: StagedCheck) -> bool {
    match check {
        StagedCheck::Skip => false,
        StagedCheck::NotRecord => false,
        StagedCheck::AuthenticateIfRecord => false,
        StagedCheck::Protected(_) => true,
    }
}

/// What the final check knows about the entries of one snapshot besides
/// their listing. The adapter answers each question about entry `i`'s own
/// blob (by object id) and path, and `staged_verdict` asks only what its
/// check needs, so an expensive answer (a read, a decryption, a lookup by
/// object id) is computed only then. An answer the adapter cannot find (a
/// failed read) is `None`, which refuses the entry.
pub trait StagedEvidence {
    /// Read entry `i`'s whole blob, which `blob` then returns; `false` if it
    /// cannot be read. Asked only when the check reads the blob
    /// (`reads_blob`).
    fn read(&mut self, i: usize) -> bool;
    /// The blob the last successful `read` read.
    fn blob(&self) -> &[u8];
    /// Whether entry `i`'s blob has this configuration's envelope: the
    /// adapter reads its size and first `ENVELOPE_PREFIX_LEN` bytes and
    /// decides with `record_envelope_prefix_ok`.
    fn is_record(&self, i: usize) -> Option<bool>;
    /// Whether entry `i`'s blob authenticates at its path under the
    /// configuration (`open_record`, with the key).
    fn opens(&self, i: usize) -> Option<bool>;
    /// Whether entry `i`'s blob is at another path of the index, `HEAD` or
    /// `HEAD^1` (`blob_elsewhere`), or, in the audit, is the blob of a path
    /// the commit deletes.
    fn elsewhere(&self, i: usize) -> Option<bool>;
}

/// Why the final check refuses an entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StagedRefusal {
    /// A protected blob without the v3 file header: plaintext.
    Plaintext,
    /// A protected record of another configuration.
    OtherConfig,
    /// A protected blob whose envelope is not a record of this configuration.
    Envelope,
    /// A protected record that does not authenticate at its path.
    Authentication,
    /// A protected record that is another path's blob (checked without the
    /// key): moved or copied without re-encryption.
    Moved,
    /// An unprotected file staged since `HEAD` that is a record of this
    /// configuration.
    UnprotectedRecord,
    /// An unprotected file that is a record of this configuration and does
    /// not authenticate at its path.
    UnprotectedForgery,
    /// An answer the check needs could not be found (a failed read).
    Unanswered,
}

/// The check of protected entry `i`, whose blob `record` has the header of
/// this configuration `id`.
fn protected_verdict<E: StagedEvidence>(
    evidence: &E,
    i: usize,
    check: EntryCheck,
    record: &[u8],
    id: &[u8; ID_LEN],
) -> Result<(), StagedRefusal> {
    match check {
        EntryCheck::Authenticate => match evidence.opens(i) {
            Some(true) => Ok(()),
            Some(false) => Err(StagedRefusal::Authentication),
            None => Err(StagedRefusal::Unanswered),
        },
        EntryCheck::Envelope => {
            if record_envelope_ok(record, id) {
                Ok(())
            } else {
                Err(StagedRefusal::Envelope)
            }
        }
        EntryCheck::EnvelopeNotMoved => {
            if !record_envelope_ok(record, id) {
                Err(StagedRefusal::Envelope)
            } else {
                match evidence.elsewhere(i) {
                    Some(false) => Ok(()),
                    Some(true) => Err(StagedRefusal::Moved),
                    None => Err(StagedRefusal::Unanswered),
                }
            }
        }
    }
}

/// Whether entry `i` passes its check (`staged_check`), for the
/// configuration `id`. `record` is the entry's blob when the check reads it
/// (`reads_blob`), and is not used otherwise. `evidence` is asked only what
/// the check needs: `is_record` only of an unprotected entry, `opens` only
/// to authenticate (an unprotected entry only once it is a record), and
/// `elsewhere` only of an entry checked without the key that has the
/// envelope. An answer that could not be found refuses (`Unanswered`).
pub fn staged_verdict<E: StagedEvidence>(
    evidence: &E,
    i: usize,
    check: StagedCheck,
    record: &[u8],
    id: &[u8; ID_LEN],
) -> Result<(), StagedRefusal> {
    match check {
        StagedCheck::Skip => Ok(()),
        StagedCheck::NotRecord => match evidence.is_record(i) {
            Some(false) => Ok(()),
            Some(true) => Err(StagedRefusal::UnprotectedRecord),
            None => Err(StagedRefusal::Unanswered),
        },
        StagedCheck::AuthenticateIfRecord => match evidence.is_record(i) {
            Some(false) => Ok(()),
            Some(true) => match evidence.opens(i) {
                Some(true) => Ok(()),
                Some(false) => Err(StagedRefusal::UnprotectedForgery),
                None => Err(StagedRefusal::Unanswered),
            },
            None => Err(StagedRefusal::Unanswered),
        },
        StagedCheck::Protected(entry) => match parse_file_header(record) {
            Err(_) => Err(StagedRefusal::Plaintext),
            Ok(found) => {
                if bytes_eq(&found, id) {
                    protected_verdict(evidence, i, entry, record, id)
                } else {
                    Err(StagedRefusal::OtherConfig)
                }
            }
        },
    }
}

/// The pre-commit hook's final check of the whole index listing (`index`,
/// `index_ends`), for the configuration `id`: every entry, in order, gets
/// its check (`staged_check`, with the run's `flags`, `in_head`,
/// `in_parent`, `keyed`, `incremental` and `guard`), its blob is read when
/// the check reads it (`reads_blob`; a failed read refuses), and it must
/// pass (`staged_verdict`). The first refusal stops the check and names the
/// entry's position.
#[allow(clippy::too_many_arguments)]
pub fn index_verdict<E: StagedEvidence>(
    evidence: &mut E,
    index: &[u8],
    index_ends: &[usize],
    flags: &[bool],
    in_head: &[bool],
    in_parent: &[bool],
    keyed: bool,
    incremental: bool,
    guard: bool,
    id: &[u8; ID_LEN],
) -> Result<(), (usize, StagedRefusal)> {
    let mut i = 0;
    while i < index_ends.len() {
        let check = staged_check(index, index_ends, i, flags, in_head, in_parent, keyed, incremental, guard);
        if reads_blob(check) && !evidence.read(i) {
            return Err((i, StagedRefusal::Unanswered));
        }
        match staged_verdict(&*evidence, i, check, evidence.blob(), id) {
            Ok(()) => i += 1,
            Err(refusal) => return Err((i, refusal)),
        }
    }
    Ok(())
}

/// Length of a pkt-line header: the packet length in hexadecimal digits.
pub const PKT_HEADER_LEN: usize = 4;
/// Largest pkt-line Git sends or accepts: 4 length digits plus 65516 data bytes.
pub const MAX_PKT_LEN: usize = 65520;
/// The radix of a pkt-line length.
const HEX_RADIX: usize = 16;
/// The value of the hexadecimal digit `a`.
const HEX_LETTER_VALUE: u8 = 10;

/// Decode the `PKT_HEADER_LEN`-byte header of a pkt-line in Git's long-running filter
/// protocol: lowercase hexadecimal total length (header included). `Ok(0)`
/// is a flush packet; otherwise the length is between 5 and `MAX_PKT_LEN`.
/// Lengths 1 to 4 (special or empty packets, which the filter protocol never
/// uses), uppercase or other digits, and oversized lengths are refused.
pub fn decode_pkt_len(header: &[u8; PKT_HEADER_LEN]) -> Result<usize, Refusal> {
    let mut value = 0;
    let mut ok = true;
    let mut i = 0;
    while ok && i < PKT_HEADER_LEN {
        let c = header[i];
        if c >= b'0' && c <= b'9' {
            value = value * HEX_RADIX + (c - b'0') as usize;
        } else if c >= b'a' && c <= b'f' {
            value = value * HEX_RADIX + (c - b'a' + HEX_LETTER_VALUE) as usize;
        } else {
            ok = false;
        }
        i += 1;
    }
    if !ok || (value != 0 && value <= PKT_HEADER_LEN) || value > MAX_PKT_LEN {
        return Err(Refusal::Request);
    }
    Ok(value)
}

// ---------------------------------------------------------------------------
// Git snapshots: the inputs of the pre-commit decisions.
//
// A *listing* is the exact output of `git ls-files --stage -z`: records
// `mode SP oid SP 0 TAB path`, each followed by NUL (tree listings are
// rewritten to the same shape by the adapter). Git prints them in byte order
// of their paths, each path once. `parse_listing` checks one and records
// where each record ends; every query below takes a listing with those
// `ends`, and is only meaningful for a listing `parse_listing` accepted.
// Path lookups are binary searches; lookups by object id use an *object
// order* of the listing (`object_order_ok`).
// ---------------------------------------------------------------------------

/// Where record `i` starts: after the NUL that ends record `i - 1`.
fn record_start(ends: &[usize], i: usize) -> usize {
    if i == 0 {
        0
    } else {
        ends[i - 1] + 1
    }
}

/// Whether `entry` is a stage-0 index record (`parse_index_entry`) whose
/// object id `entry[OID_START..path_start - OID_END_LEN]` passes `is_object_id`.
fn record_ok(entry: &[u8]) -> bool {
    match parse_index_entry(entry) {
        Ok(parsed) => is_object_id(&entry[OID_START..parsed.path_start - OID_END_LEN]),
        Err(_) => false,
    }
}

/// Whether `a` comes before `b` in byte order, which is Git's order of
/// paths: at the first position where they differ `a` has the smaller byte,
/// or `a` is a proper prefix of `b`.
pub fn bytes_lt(a: &[u8], b: &[u8]) -> bool {
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
        i += 1;
    }
    a.len() < b.len()
}

/// Whether the records of a listing with `ends` are in byte order of their
/// paths: strictly increasing (`unique`, each path once) or never
/// decreasing.
fn listing_ordered(listing: &[u8], ends: &[usize], unique: bool) -> bool {
    let mut i = 1;
    while i < ends.len() {
        match listing_fields(listing, ends, i - 1) {
            Some(p) => match listing_fields(listing, ends, i) {
                Some(f) => {
                    let previous = &listing[p.path_start..p.end];
                    let path = &listing[f.path_start..f.end];
                    let ordered = if unique {
                        bytes_lt(previous, path)
                    } else {
                        bytes_lt(previous, path) | bytes_eq(previous, path)
                    };
                    if !ordered {
                        return false;
                    }
                }
                None => return false,
            },
            None => return false,
        }
        i += 1;
    }
    true
}

/// Check that `listing` is exactly `ends.len()` NUL-terminated index records
/// (`record_ok`, so every mode, object id and path is well formed) in byte
/// order of their paths, each path once if `unique` (`listing_ordered`), and
/// record in `ends[i]` the position of the NUL that ends record `i`. On
/// failure `ends` must not be used. Git lists the index and each tree with
/// unique paths; only the adapter's merge of several trees repeats them.
pub fn parse_listing(listing: &[u8], ends: &mut [usize], unique: bool) -> bool {
    let mut ok = true;
    let mut start = 0;
    let mut i = 0;
    while ok && i < ends.len() {
        let end = find_byte(listing, start, b'\0');
        if end < listing.len() && record_ok(&listing[start..end]) {
            ends[i] = end;
            start = end + 1;
            i += 1;
        } else {
            ok = false;
        }
    }
    if ok && start == listing.len() {
        listing_ordered(listing, ends, unique)
    } else {
        false
    }
}

/// The fields of one listing record: the record is `listing[start..end]`,
/// its object id `listing[start + OID_START..oid_end]`, its path
/// `listing[path_start..end]`, and `regular` says whether its mode is
/// `100644` or `100755`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fields {
    pub start: usize,
    pub oid_end: usize,
    pub path_start: usize,
    pub end: usize,
    pub regular: bool,
}

/// The fields of record `i` of a listing that `parse_listing` accepted with
/// `ends`. The path starts after the first TAB (modes and object ids have
/// none).
pub fn listing_fields(listing: &[u8], ends: &[usize], i: usize) -> Option<Fields> {
    if i >= ends.len() {
        return None;
    }
    let start = record_start(ends, i);
    let end = ends[i];
    let tab = find_byte(listing, start, b'\t');
    if end > listing.len() || tab >= end || tab - start < ENTRY_FIXED_LEN {
        return None;
    }
    let regular = matches_at(listing, start, &REGULAR_MODE) || matches_at(listing, start, &EXECUTABLE_MODE);
    let path_start = tab + 1;
    Some(Fields { start, oid_end: path_start - OID_END_LEN, path_start, end, regular })
}

/// Whether the record `listing[start..end]` names object `oid`, and is at
/// `path` (`same_path`) or at another path (`!same_path`). `oid` contains no
/// TAB, so a record names it exactly when `oid SP 0 TAB` follows its mode.
fn record_is(listing: &[u8], start: usize, end: usize, oid: &[u8], path: &[u8], same_path: bool) -> bool {
    if start > end || end > listing.len() || end - start < ENTRY_FIXED_LEN || end - start - ENTRY_FIXED_LEN < oid.len() {
        return false;
    }
    let at = start + OID_START + oid.len();
    if !matches_at(listing, start + OID_START, oid) || !matches_at(listing, at, &OID_END) {
        return false;
    }
    let here = end - at - OID_END_LEN == path.len() && matches_at(listing, at + OID_END_LEN, path);
    here == same_path
}

/// Whether record `j` exists and its path comes before `path`.
fn path_before(listing: &[u8], ends: &[usize], j: usize, path: &[u8]) -> bool {
    match listing_fields(listing, ends, j) {
        Some(f) => bytes_lt(&listing[f.path_start..f.end], path),
        None => false,
    }
}

/// Whether record `j` exists and is at `path`.
fn path_at(listing: &[u8], ends: &[usize], j: usize, path: &[u8]) -> bool {
    match listing_fields(listing, ends, j) {
        Some(f) => bytes_eq(&listing[f.path_start..f.end], path),
        None => false,
    }
}

/// The first record whose path does not come before `path`, or
/// `ends.len()`: a binary search of a listing in path order.
fn find_path(listing: &[u8], ends: &[usize], path: &[u8]) -> usize {
    let mut low = 0;
    let mut high = ends.len();
    while low < high {
        let middle = low + (high - low) / 2;
        if path_before(listing, ends, middle, path) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    low
}

/// The position of a record that names `oid` at `path`, or `ends.len()` if
/// there is none, in a listing in path order: the records at `path` are the
/// ones from `find_path` on.
fn find_entry(listing: &[u8], ends: &[usize], oid: &[u8], path: &[u8]) -> usize {
    let mut j = find_path(listing, ends, path);
    while j < ends.len() && path_at(listing, ends, j, path) {
        if record_is(listing, record_start(ends, j), ends[j], oid, path, true) {
            return j;
        }
        j += 1;
    }
    ends.len()
}

/// For each record `i` of the listing `index` with `wanted[i]`, whether the
/// listing `other` holds a record with its object id and path
/// (`held[i]`); `held[i]` is false for the others. Fails, writing nothing,
/// unless `wanted` and `held` have one slot per record. `other` must be in
/// path order (`parse_listing`, possibly not `unique`).
pub fn held_entries(
    index: &[u8],
    index_ends: &[usize],
    wanted: &[bool],
    other: &[u8],
    other_ends: &[usize],
    held: &mut [bool],
) -> bool {
    if wanted.len() != index_ends.len() || held.len() != index_ends.len() {
        return false;
    }
    let mut i = 0;
    while i < held.len() {
        if wanted[i] {
            match listing_fields(index, index_ends, i) {
                Some(f) => {
                    let j = find_entry(other, other_ends, &index[f.start + OID_START..f.oid_end], &index[f.path_start..f.end]);
                    held[i] = j < other_ends.len();
                }
                None => held[i] = false,
            }
        } else {
            held[i] = false;
        }
        i += 1;
    }
    true
}

/// For each record `i` of the listing `index` with `wanted[i]`, whether the
/// listing `other` holds exactly that record: the same mode, object id and
/// path (`held[i]`); `held[i]` is false for the others. Unlike
/// `held_entries`, a record whose mode changed (a symlink staged as a file
/// with the same blob) is not held. Fails, writing nothing, unless `wanted`
/// and `held` have one slot per record. `other` must be in path order with
/// each path once (`parse_listing` with `unique`).
pub fn held_records(
    index: &[u8],
    index_ends: &[usize],
    wanted: &[bool],
    other: &[u8],
    other_ends: &[usize],
    held: &mut [bool],
) -> bool {
    if wanted.len() != index_ends.len() || held.len() != index_ends.len() {
        return false;
    }
    let mut i = 0;
    while i < held.len() {
        if wanted[i] {
            match listing_fields(index, index_ends, i) {
                Some(f) => {
                    let j = find_entry(other, other_ends, &index[f.start + OID_START..f.oid_end], &index[f.path_start..f.end]);
                    held[i] = j < other_ends.len() && same_record(index, index_ends, i, other, other_ends, j);
                }
                None => held[i] = false,
            }
        } else {
            held[i] = false;
        }
        i += 1;
    }
    true
}

/// The provenance of a staged protected entry: `in_head`, `HEAD` holds its
/// blob at its path; `incoming_known`, the commits being merged, picked,
/// reverted or rebased are known, and `in_incoming`, one of them holds it;
/// `forced`, `protect` selected it. The user's change takes precedence over
/// `forced`, which can only add sealing plaintext.
pub fn provenance_of(in_head: bool, incoming_known: bool, in_incoming: bool, forced: bool) -> Provenance {
    if !in_head && incoming_known && !in_incoming {
        Provenance::Local
    } else if forced {
        Provenance::Forced
    } else if !in_head && !incoming_known {
        Provenance::Unknown
    } else {
        Provenance::Committed
    }
}

/// The provenance (`provenance_of`) of entry `i` of the listing `index`:
/// whether the listing `head` holds its blob at its path and, when
/// `incoming_known`, whether the listing `incoming` (the commits being
/// brought in, as one listing) does; `forced`, `protect` selected it. Both
/// listings must be in path order (`parse_listing`, possibly not `unique`);
/// `incoming` is not read unless `incoming_known`. An `i` past the end is
/// `Committed`, which is never repaired.
#[allow(clippy::too_many_arguments)]
pub fn entry_provenance(
    index: &[u8],
    index_ends: &[usize],
    i: usize,
    head: &[u8],
    head_ends: &[usize],
    incoming: &[u8],
    incoming_ends: &[usize],
    incoming_known: bool,
    forced: bool,
) -> Provenance {
    match listing_fields(index, index_ends, i) {
        Some(f) => {
            let oid = &index[f.start + OID_START..f.oid_end];
            let path = &index[f.path_start..f.end];
            let in_head = find_entry(head, head_ends, oid, path) < head_ends.len();
            let in_incoming = if incoming_known {
                find_entry(incoming, incoming_ends, oid, path) < incoming_ends.len()
            } else {
                false
            };
            provenance_of(in_head, incoming_known, in_incoming, forced)
        }
        None => Provenance::Committed,
    }
}

/// Whether record `j` exists and its key, its object id and then its
/// position, comes before the key `(oid, at)`.
fn object_before(listing: &[u8], ends: &[usize], j: usize, oid: &[u8], at: usize) -> bool {
    match listing_fields(listing, ends, j) {
        Some(f) => {
            let id = &listing[f.start + OID_START..f.oid_end];
            bytes_lt(id, oid) | (bytes_eq(id, oid) & (j < at))
        }
        None => false,
    }
}

/// Whether `order` lists the records of a listing by object id, and by
/// position among equal ids: one slot per record, and the keys of
/// `order[0]`, `order[1]`, … strictly increase (`object_before`), so every
/// record is listed exactly once. The adapter sorts; this checks.
pub fn object_order_ok(listing: &[u8], ends: &[usize], order: &[usize]) -> bool {
    if order.len() != ends.len() {
        return false;
    }
    let mut t = 0;
    while t < order.len() {
        let j = order[t];
        match listing_fields(listing, ends, j) {
            Some(f) => {
                if t > 0 && !object_before(listing, ends, order[t - 1], &listing[f.start + OID_START..f.oid_end], j) {
                    return false;
                }
            }
            None => return false,
        }
        t += 1;
    }
    true
}

/// The first slot `t` of an object order (`object_order_ok`) whose record's
/// key is not before `(oid, at)`, or `order.len()`: a binary search. The
/// records of `oid` at positions from `at` on are the ones from there on.
fn find_object(listing: &[u8], ends: &[usize], order: &[usize], oid: &[u8], at: usize) -> usize {
    let mut low = 0;
    let mut high = order.len();
    while low < high {
        let middle = low + (high - low) / 2;
        if object_before(listing, ends, order[middle], oid, at) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    low
}

/// Whether record `j` exists and names `oid`.
fn names_oid(listing: &[u8], ends: &[usize], j: usize, oid: &[u8]) -> bool {
    match listing_fields(listing, ends, j) {
        Some(f) => bytes_eq(&listing[f.start + OID_START..f.oid_end], oid),
        None => false,
    }
}

/// Whether record `j` of `head` is a source the staged blob `oid` at `path`
/// may have been moved from: it names `oid` at another path, and the index
/// does not hold that blob at that path (the entry is gone or replaced).
fn move_source_at(
    index: &[u8],
    index_ends: &[usize],
    head: &[u8],
    head_ends: &[usize],
    oid: &[u8],
    path: &[u8],
    j: usize,
) -> bool {
    let start = record_start(head_ends, j);
    if !record_is(head, start, head_ends[j], oid, path, false) {
        return false;
    }
    let source = &head[start + ENTRY_FIXED_LEN + oid.len()..head_ends[j]];
    find_entry(index, index_ends, oid, source) == index_ends.len()
}

/// The first move source (`move_source_at`) among the records
/// `head_order[t]`, `head_order[t + 1]`, … that name `oid`, or
/// `head_ends.len()`.
#[allow(clippy::too_many_arguments)]
fn move_source_from(
    index: &[u8],
    index_ends: &[usize],
    head: &[u8],
    head_ends: &[usize],
    head_order: &[usize],
    oid: &[u8],
    path: &[u8],
    t: usize,
) -> usize {
    let mut t = t;
    while t < head_order.len() && names_oid(head, head_ends, head_order[t], oid) {
        let j = head_order[t];
        if move_source_at(index, index_ends, head, head_ends, oid, path, j) {
            return j;
        }
        t += 1;
    }
    head_ends.len()
}

/// The next record of `head`, from position `from` on, that the staged entry
/// `i` of `index` may have been moved from (`move_source_at`), or
/// `head_ends.len()` if there is none. The hook tries the candidates in
/// `HEAD` order and re-encrypts from the first at which the record opens.
/// `head_order` is an object order of `head` (`object_order_ok`): the
/// candidates are the records of the blob from `from` on, in that order.
pub fn next_move_source(
    index: &[u8],
    index_ends: &[usize],
    i: usize,
    head: &[u8],
    head_ends: &[usize],
    head_order: &[usize],
    from: usize,
) -> usize {
    match listing_fields(index, index_ends, i) {
        Some(f) => {
            let oid = &index[f.start + OID_START..f.oid_end];
            let path = &index[f.path_start..f.end];
            let t = find_object(head, head_ends, head_order, oid, from);
            move_source_from(index, index_ends, head, head_ends, head_order, oid, path, t)
        }
        None => head_ends.len(),
    }
}

/// Whether slot `t` of an object order names a record of `oid` at another
/// path than `path`.
fn other_path_at(listing: &[u8], ends: &[usize], order: &[usize], t: usize, oid: &[u8], path: &[u8]) -> bool {
    if t < order.len() && order[t] < ends.len() {
        let j = order[t];
        record_is(listing, record_start(ends, j), ends[j], oid, path, false)
    } else {
        false
    }
}

/// Whether a listing with unique paths holds `oid` at another path than
/// `path`. Its records of `oid` are together in the object order, at most
/// one of them at `path`, so one of the first two is elsewhere if any is.
fn elsewhere_in(listing: &[u8], ends: &[usize], order: &[usize], oid: &[u8], path: &[u8]) -> bool {
    let t = find_object(listing, ends, order, oid, 0);
    if t < order.len() {
        other_path_at(listing, ends, order, t, oid, path) | other_path_at(listing, ends, order, t + 1, oid, path)
    } else {
        false
    }
}

/// Whether the blob of entry `i` of `index` is at another path in `index`,
/// `head` or `parent`: a record moved or copied there, which only the key
/// can re-encrypt (the locked pre-commit check refuses it). Each listing
/// comes with an object order (`object_order_ok`).
#[allow(clippy::too_many_arguments)]
pub fn blob_elsewhere(
    index: &[u8],
    index_ends: &[usize],
    index_order: &[usize],
    i: usize,
    head: &[u8],
    head_ends: &[usize],
    head_order: &[usize],
    parent: &[u8],
    parent_ends: &[usize],
    parent_order: &[usize],
) -> bool {
    match listing_fields(index, index_ends, i) {
        Some(f) => {
            let oid = &index[f.start + OID_START..f.oid_end];
            let path = &index[f.path_start..f.end];
            elsewhere_in(index, index_ends, index_order, oid, path)
                | elsewhere_in(head, head_ends, head_order, oid, path)
                | elsewhere_in(parent, parent_ends, parent_order, oid, path)
        }
        None => false,
    }
}

/// Parse Git's `check-attr -z --stdin filter` answer for the paths of the
/// records of `listing`, in order: one `parse_attr_record` per record and
/// nothing else. Then `flags[i]` says whether record `i` is protected. The
/// answer is checked against the listing's own paths, so it cannot describe
/// any other file. On failure the flags must not be used.
pub fn parse_listing_attrs(listing: &[u8], ends: &[usize], response: &[u8], flags: &mut [bool]) -> bool {
    let mut ok = flags.len() == ends.len();
    let mut at = 0;
    let mut i = 0;
    while ok && i < flags.len() {
        match listing_fields(listing, ends, i) {
            Some(f) => match parse_attr_record(response, at, &listing[f.path_start..f.end]) {
                Ok(record) => {
                    flags[i] = record.protected;
                    at = record.next;
                    i += 1;
                }
                Err(_) => ok = false,
            },
            None => ok = false,
        }
    }
    ok && at == response.len()
}

/// The first protected record (`flags`) that cannot be protected: not a
/// regular file (a symlink or submodule, which Git stores unfiltered) or
/// reserved metadata (`is_reserved_path`); `flags.len()` if there is none.
pub fn first_unselectable(listing: &[u8], ends: &[usize], flags: &[bool]) -> usize {
    let mut i = 0;
    let mut bad = false;
    while !bad && i < flags.len() {
        if flags[i] {
            match listing_fields(listing, ends, i) {
                Some(f) => bad = !f.regular | is_reserved_path(&listing[f.path_start..f.end]),
                None => bad = true,
            }
        }
        if !bad {
            i += 1;
        }
    }
    i
}

/// Whether record `j` exists and is at a policy path (`is_policy_path`).
fn policy_at(listing: &[u8], ends: &[usize], j: usize) -> bool {
    match listing_fields(listing, ends, j) {
        Some(f) => is_policy_path(&listing[f.path_start..f.end]),
        None => false,
    }
}

/// The first record at a policy path from position `from` on, or
/// `ends.len()` if there is none.
fn next_policy(listing: &[u8], ends: &[usize], from: usize) -> usize {
    let mut j = from;
    while j < ends.len() && !policy_at(listing, ends, j) {
        j += 1;
    }
    j
}

/// Whether record `i` of `a` and record `j` of `b` exist and are the same
/// record: the same mode, object id and path.
fn same_record(a: &[u8], a_ends: &[usize], i: usize, b: &[u8], b_ends: &[usize], j: usize) -> bool {
    match listing_fields(a, a_ends, i) {
        Some(f) => match listing_fields(b, b_ends, j) {
            Some(g) => bytes_eq(&a[f.start..f.end], &b[g.start..g.end]),
            None => false,
        },
        None => false,
    }
}

/// Whether the listings `a` and `b` have the same records at policy paths,
/// in the same order.
fn same_policy(a: &[u8], a_ends: &[usize], b: &[u8], b_ends: &[usize]) -> bool {
    let mut i = next_policy(a, a_ends, 0);
    let mut j = next_policy(b, b_ends, 0);
    while i < a_ends.len() && j < b_ends.len() {
        if !same_record(a, a_ends, i, b, b_ends, j) {
            return false;
        }
        i = next_policy(a, a_ends, i + 1);
        j = next_policy(b, b_ends, j + 1);
    }
    i == a_ends.len() && j == b_ends.len()
}

/// Whether the index, `HEAD` and `HEAD^1` (`parent`) have exactly the same
/// records at policy paths (`is_policy_path`: every attribute file and the
/// configuration, each with its mode and object id). The pre-commit hook
/// counts an entry unchanged since `HEAD` and `HEAD^1` as settled, and does
/// not authenticate it again, only while this holds: the entry was checked
/// when it was committed only if what selected it, and the configuration it
/// was checked under, were the same then. This compares committed bytes;
/// it does not interpret the attributes.
pub fn policy_unchanged(
    index: &[u8],
    index_ends: &[usize],
    head: &[u8],
    head_ends: &[usize],
    parent: &[u8],
    parent_ends: &[usize],
) -> bool {
    same_policy(index, index_ends, head, head_ends) & same_policy(index, index_ends, parent, parent_ends)
}

// ---------------------------------------------------------------------------
// The stored key and Git object replies.
// ---------------------------------------------------------------------------

/// Length of the derived AES-SIV key.
pub const KEY_LEN: usize = 64;
/// The associated-data path of the stored key's check value. It is reserved
/// metadata (in `METADATA_DIR`), so no record is ever sealed or opened at
/// it: the check value is no record, and no record is a check value.
pub const KEY_CHECK_PATH: [u8; 21] = *b".transcrypt/key-check";
/// Length of `KEY_CHECK_PLAINTEXT`.
pub const KEY_CHECK_PLAINTEXT_LEN: usize = 23;
/// The plaintext of the check value. It is not empty, so opening the check
/// value decrypts it with the CTR half of the key and verifies its tag over
/// the result with the S2V half (RFC 5297): unlike the configuration tag
/// (the encryption of the empty plaintext), it involves the whole key.
pub const KEY_CHECK_PLAINTEXT: [u8; 23] = *b"transcrypt/v3/key-check";
// Literal lengths, as for `CONFIG_LEN` (`literal_lengths_are_the_field_sums`).
/// The check value: the tag, then the encrypted `KEY_CHECK_PLAINTEXT`
/// (39 = 16 + 23).
pub const KEY_CHECK_LEN: usize = 39;
/// Where the check value starts in the stored key file: after the config
/// and the key (119 = 55 + 64).
pub const KEY_CHECK_START: usize = 119;
/// Length of the stored key file: the public config it unlocks, the key,
/// and the key's check value for that config (158 = 55 + 64 + 39). A file
/// of the earlier layout, the config and the key (119 bytes), is damaged.
pub const KEY_FILE_LEN: usize = 158;

/// What the stored key file means for the current configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoredKey {
    /// No stored key: no file, or one an earlier version wrote (the key
    /// alone, without its config). The private-mode agent is asked.
    Absent,
    /// A file of any other length: refused until `unlock` rewrites it.
    Damaged,
    /// A key for another configuration (a pulled `rekey`), or one that does
    /// not authenticate it: locked until `unlock`.
    Stale,
    /// The key was stored for exactly this configuration and authenticates
    /// it.
    Unlocked,
}

/// Decide what the stored key file means for configuration `current`.
/// `present`: the file exists; `file`: its bytes (the adapter reads at most
/// one byte more than `KEY_FILE_LEN`); `authentic`: the key
/// `file[CONFIG_LEN..KEY_CHECK_START]` authenticates `current`
/// (`authenticate_config`) and the check value `file[KEY_CHECK_START..]`
/// opens under it (`key_check_opens`), which matters only for a file of
/// `KEY_FILE_LEN` bytes. A key is used only for the configuration it was
/// stored with, and only once it authenticates it and its check value.
pub fn stored_key_state(present: bool, file: &[u8], current: &[u8], authentic: bool) -> StoredKey {
    if !present || file.len() == KEY_LEN {
        return StoredKey::Absent;
    }
    if file.len() != KEY_FILE_LEN {
        return StoredKey::Damaged;
    }
    if !bytes_eq(&file[0..CONFIG_LEN], current) || !authentic {
        return StoredKey::Stale;
    }
    StoredKey::Unlocked
}

/// The construction of primitives from one derived key. The adapter's
/// implementation must give primitives that realize the cryptographic
/// contract under exactly the key bytes it is passed (A5, A17).
pub trait V3KeySchedule: Sized {
    /// The primitives under the `KEY_LEN`-byte `key`; `None` for a key of
    /// another length, or if they cannot be built.
    fn from_key(key: &[u8]) -> Option<Self>;
}

/// The check value of the stored key file for `config` under `primitives`
/// (those of the key stored with it): `KEY_CHECK_PLAINTEXT` sealed at
/// `KEY_CHECK_PATH` under `config`.
pub fn seal_key_check<P: V3Primitives>(primitives: &P, config: &[u8; CONFIG_LEN]) -> Result<[u8; KEY_CHECK_LEN], Refusal> {
    let mut check = [0u8; KEY_CHECK_LEN];
    if !primitives.seal_file(config, &KEY_CHECK_PATH, &KEY_CHECK_PLAINTEXT, &mut check) {
        return Err(Refusal::Primitive);
    }
    Ok(check)
}

/// Whether `check` is the check value of `config` under `primitives`: it
/// opens at `KEY_CHECK_PATH` under `config`, to exactly
/// `KEY_CHECK_PLAINTEXT`.
pub fn key_check_opens<P: V3Primitives>(primitives: &P, config: &[u8; CONFIG_LEN], check: &[u8]) -> bool {
    let mut plaintext = [0u8; KEY_CHECK_PLAINTEXT_LEN];
    primitives.open_file(config, &KEY_CHECK_PATH, check, &mut plaintext) && bytes_eq(&plaintext, &KEY_CHECK_PLAINTEXT)
}

/// The primitives of `key`, only if they authenticate `config`: the single
/// way the adapter obtains primitives to use with a configuration, whether
/// the key was just derived from a passphrase or read from the stored file.
pub fn authenticate_key<P: V3Primitives + V3KeySchedule>(key: &[u8], config: &[u8; CONFIG_LEN]) -> Result<P, Refusal> {
    let primitives = match P::from_key(key) {
        Some(primitives) => primitives,
        None => return Err(Refusal::Primitive),
    };
    if let Err(refusal) = authenticate_config(&primitives, config) {
        return Err(refusal);
    }
    Ok(primitives)
}

/// The stored key for configuration `current` (inputs as for
/// `stored_key_state`), with the primitives it selects: `Ok` exactly when
/// `stored_key_state` says `Unlocked`, and then the primitives are those of
/// the key bytes `file[CONFIG_LEN..KEY_CHECK_START]`, which authenticate
/// `current` and under which the file's check value opens, together with
/// the configuration they authenticated (the bytes of `current`).
/// Otherwise the state, never `Unlocked`.
pub fn unlock_stored_key<P: V3Primitives + V3KeySchedule>(
    present: bool,
    file: &[u8],
    current: &[u8],
) -> Result<(P, [u8; CONFIG_LEN]), StoredKey> {
    if !present || file.len() != KEY_FILE_LEN || current.len() != CONFIG_LEN {
        return Err(stored_key_state(present, file, current, false));
    }
    let mut config = [0u8; CONFIG_LEN];
    let mut i = 0;
    while i < CONFIG_LEN {
        config[i] = current[i];
        i += 1;
    }
    match authenticate_key::<P>(&file[CONFIG_LEN..KEY_CHECK_START], &config) {
        Ok(primitives) => {
            let checked = key_check_opens(&primitives, &config, &file[KEY_CHECK_START..KEY_FILE_LEN]);
            match stored_key_state(present, file, current, checked) {
                StoredKey::Unlocked => Ok((primitives, config)),
                state => Err(state),
            }
        }
        Err(_) => Err(stored_key_state(present, file, current, false)),
    }
}

/// Length of `BLOB_FIELD`.
const BLOB_FIELD_LEN: usize = 6;
/// The type field of a `cat-file --batch` reply for a blob.
const BLOB_FIELD: [u8; BLOB_FIELD_LEN] = *b" blob ";
/// The most decimal digits of a blob size in a reply: every number with
/// that many digits fits in a `u64`.
const MAX_SIZE_DIGITS: usize = 19;
/// The radix of a blob size.
const DECIMAL_RADIX: u64 = 10;

/// The value of the decimal digits `bytes[from..to]` (at most
/// `MAX_SIZE_DIGITS`, so it fits in 64 bits), or `None` if one of them is
/// not a digit.
fn decimal(bytes: &[u8], from: usize, to: usize) -> Option<u64> {
    let mut value: u64 = 0;
    let mut ok = true;
    let mut i = from;
    while ok && i < to {
        let c = bytes[i];
        if c >= b'0' && c <= b'9' {
            value = value * DECIMAL_RADIX + (c - b'0') as u64;
            i += 1;
        } else {
            ok = false;
        }
    }
    if ok {
        Some(value)
    } else {
        None
    }
}

/// The size in Git's `cat-file --batch` reply header for object `oid`, which
/// must be exactly `<oid> SP blob SP <size> LF` with `<size>` in canonical
/// decimal (digits only, no leading zero) of at most `MAX_SIZE_DIGITS` digits. A missing
/// object, another type, another object id or any other header is refused,
/// so bytes are never attributed to the wrong object.
pub fn parse_batch_header(header: &[u8], oid: &[u8]) -> Option<u64> {
    if !matches_at(header, 0, oid) || !matches_at(header, oid.len(), &BLOB_FIELD) {
        return None;
    }
    // Both matched, so `digits <= header.len()`.
    let digits = oid.len() + BLOB_FIELD_LEN;
    let n = header.len();
    // The digits, then LF.
    if n == digits || header[n - 1] != b'\n' {
        return None;
    }
    let lf = n - 1;
    let count = lf - digits;
    if count == 0 || count > MAX_SIZE_DIGITS {
        return None;
    }
    if header[digits] == b'0' && count != 1 {
        return None;
    }
    decimal(header, digits, lf)
}

/// How to read the content of a blob of `size` bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlobRead {
    /// Read it: it may be a v3 record.
    Read,
    /// Skip it unread: larger than any record, and the caller allows that.
    Skip,
    /// Refuse: larger than any record.
    TooLarge,
}

/// The read decision for a blob of `size` bytes: only blobs within the
/// record bound are ever loaded.
pub fn blob_read(size: u64, skip_large: bool) -> BlobRead {
    if size <= MAX_RECORD as u64 {
        BlobRead::Read
    } else if skip_large {
        BlobRead::Skip
    } else {
        BlobRead::TooLarge
    }
}

/// What the audit of one commit may take from its first parent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuditBase {
    /// Nothing: a root commit, or a commit that changes the configuration.
    /// The audit examines its whole tree and trusts no entry.
    Tree,
    /// The first parent, under the same configuration, whose records
    /// authenticate at their paths: checked by the keyed audit before this
    /// commit, or outside the audited range and trusted (already published,
    /// or deliberately excluded). An unprotected file the parent holds
    /// exactly needs no check.
    Parent,
}

/// What the audit knows about one entry of a commit it examines, each
/// fact about the entry itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuditedEntry {
    /// Its mode is `100644` or `100755`: a file Git filters.
    pub regular: bool,
    /// The commit's own attributes select its path (`filter=transcrypt-v3`).
    pub selected: bool,
    /// The first parent holds exactly this entry: path, mode and blob.
    pub held: bool,
    /// Its blob is that of a path the commit deletes: moved there without
    /// re-encryption.
    pub moved: bool,
}

/// The audit's check of one entry of a commit, in the pre-commit hook's
/// vocabulary (`StagedCheck`, decided by `staged_verdict`), or `None` to
/// refuse: a selected path that is not a regular file. `keyed`: the audit
/// has the key of the commit's configuration. With the key, the audit keeps
/// the hook's invariant (`RecordsAuthentic`): every regular, non-reserved
/// entry whose blob has this configuration's envelope authenticates at its
/// own path. A selected entry is authenticated (`entry_check`, not
/// incremental: the audit never trusts a protected entry's record); an
/// unprotected file the parent holds exactly is trusted from `base`; any
/// other unprotected file is authenticated if it is a record. Without the
/// key only envelopes are checked: a selected entry has this
/// configuration's envelope and, unless the parent holds it, is not a
/// moved blob; an unprotected file is refused only if it is a moved record.
/// Repository metadata is never encrypted and never checked.
pub fn audit_check(entry: AuditedEntry, path: &[u8], keyed: bool, base: AuditBase) -> Option<StagedCheck> {
    let trusted = match base {
        AuditBase::Tree => false,
        AuditBase::Parent => entry.held,
    };
    if is_reserved_path(path) {
        Some(StagedCheck::Skip)
    } else if entry.selected {
        if entry.regular {
            Some(StagedCheck::Protected(entry_check(keyed, false, entry.held)))
        } else {
            None
        }
    } else if !entry.regular || trusted {
        Some(StagedCheck::Skip)
    } else if keyed {
        Some(StagedCheck::AuthenticateIfRecord)
    } else if entry.moved && !entry.held {
        Some(StagedCheck::NotRecord)
    } else {
        Some(StagedCheck::Skip)
    }
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests;
