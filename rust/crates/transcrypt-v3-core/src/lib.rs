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

/// Paths that are never protected, whatever the attributes say: anything in
/// `.transcrypt/` (the public configuration), every `.gitattributes` (Git
/// reads the staged blob to decide what is protected) and `.gitmodules`.
/// Which other paths are protected is the user's choice, made with Git
/// attributes (`filter=transcrypt-v3`); see `parse_attr_record`.
pub fn is_reserved_path(path: &[u8]) -> bool {
    matches_at(path, 0, &METADATA_DIR)
        || bytes_eq(path, &ATTRIBUTES_NAME)
        || ends_with(path, &ATTRIBUTES_SUFFIX)
        || bytes_eq(path, &MODULES_NAME)
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

/// What the pre-commit hook does with one staged protected entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SealAction {
    /// The staged blob already opens at its own path.
    Keep,
    /// Seal the staged blob, which is plaintext, at its path.
    Seal,
    /// Re-seal, for this path, the plaintext of a record moved here.
    Rebind,
    /// Change nothing; verification decides (and refuses a bad record).
    Leave,
}

/// The pre-commit repair decision. `opens`: the staged blob opens at its
/// own path. `local_change`: the user staged it (it differs from `HEAD`'s
/// blob there and no merge, cherry-pick, revert or rebase is in progress),
/// or `protect` selected it. `envelope`: it has the v3 file header.
/// `moved`: it opens at a `HEAD` path that is no longer in the index. Only a
/// local change is ever sealed or re-sealed: content that came from a
/// commit is checked, never repaired, so a hostile move cannot be laundered
/// into a genuine record.
pub fn seal_action(opens: bool, local_change: bool, envelope: bool, moved: bool) -> SealAction {
    if opens {
        SealAction::Keep
    } else if !local_change {
        SealAction::Leave
    } else if !envelope {
        SealAction::Seal
    } else if moved {
        SealAction::Rebind
    } else {
        SealAction::Leave
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

/// The pre-commit hook's `local_change` input of `seal_action` for one
/// staged protected entry: the user staged it (`HEAD` does not hold its blob
/// at its path, the commits being merged, picked, reverted or rebased are
/// known and do not hold it either), or `protect` forced it and it is
/// plaintext (no `envelope`). `in_head` and `in_incoming` come from
/// `held_entries`.
pub fn is_local_change(in_head: bool, incoming_known: bool, in_incoming: bool, forced: bool, envelope: bool) -> bool {
    (!in_head & incoming_known & !in_incoming) | (forced & !envelope)
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

// ---------------------------------------------------------------------------
// The stored key and Git object replies.
// ---------------------------------------------------------------------------

/// Length of the derived AES-SIV key.
pub const KEY_LEN: usize = 64;
/// Length of the stored key file: the public config it unlocks, then the
/// key (119 = 55 + 64).
pub const KEY_FILE_LEN: usize = 119;

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
/// `file[CONFIG_LEN..]` authenticates `current` (`authenticate_config`), which
/// matters only for a file of `KEY_FILE_LEN` bytes. A key is used only for
/// the configuration it was stored with, and only once it authenticates it.
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

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_lengths_are_the_field_sums() {
        assert_eq!(CONFIG_PREFIX_LEN, CONFIG_MAGIC.len() + SALT_LEN);
        assert_eq!(CONFIG_LEN, CONFIG_PREFIX_LEN + TAG_LEN);
        assert_eq!(FILE_HEADER_LEN, FILE_MAGIC.len() + ID_LEN);
        assert_eq!(FRAME_CONFIG_START, size_of::<u8>());
        assert_eq!(FRAME_LEN_START, FRAME_CONFIG_START + CONFIG_LEN);
        assert_eq!(BE_U32_LEN, size_of::<u32>());
        assert_eq!(BLOB_FIELD_LEN, BLOB_FIELD.len());
        assert_eq!(MAX_SIZE_DIGITS, u64::MAX.ilog10() as usize);
    }

    #[test]
    fn config_codec_roundtrip_strict_length_and_magic() {
        let salt = core::array::from_fn(|i| i as u8);
        let tag = core::array::from_fn(|i| (255 - i) as u8);
        let config = Config { salt, tag };
        let bytes = encode_config(&config);
        assert_eq!(decode_config_exact(&bytes), Ok(config));
        assert_eq!(parse_config(&bytes), Ok(config));
        for n in 0..CONFIG_LEN {
            assert_eq!(parse_config(&bytes[..n]), Err(FormatError::Length));
        }
        let mut extended = bytes.to_vec();
        extended.push(1);
        assert_eq!(parse_config(&extended), Err(FormatError::Length));
        // Each byte of the version marker must be enforced, with no
        // exceptions for offsets 5 or 6 and no fallback to older formats.
        for pos in 0..CONFIG_MAGIC.len() {
            let mut modified = bytes;
            modified[pos] ^= 1;
            assert_eq!(decode_config_exact(&modified), Err(FormatError::Magic));
            assert_eq!(parse_config(&modified), Err(FormatError::Magic));
        }
    }

    #[test]
    fn file_header_codec_roundtrip_strict_length_and_magic() {
        let id = core::array::from_fn(|i| (i * 11) as u8);
        let header = encode_file_header(&id);
        assert_eq!(decode_file_header_exact(&header), Ok(id));
        for n in [FILE_MIN_LEN, FILE_MIN_LEN + 1, FILE_MIN_LEN + 255] {
            let mut blob = header.to_vec();
            blob.resize(n, 0x7f);
            assert_eq!(parse_file_header(&blob), Ok(id));
        }
        let mut record = header.to_vec();
        record.extend_from_slice(&[0x66; TAG_LEN]);
        for n in 0..FILE_MIN_LEN {
            assert_eq!(parse_file_header(&record[..n]), Err(FormatError::Length));
        }
        for pos in 0..FILE_MAGIC.len() {
            let mut modified = header;
            modified[pos] ^= 1;
            assert_eq!(decode_file_header_exact(&modified), Err(FormatError::Magic));
            let mut blob = modified.to_vec();
            blob.extend_from_slice(&[0u8; TAG_LEN]);
            assert_eq!(parse_file_header(&blob), Err(FormatError::Magic));
        }
    }

    /// A deterministic toy primitive: NOT cryptography. It exists only so the
    /// decision core can be exercised without the adapter's RustCrypto stack.
    /// The "tag" mixes key, config, path and plaintext so that changing any
    /// one of them makes `open_file` fail, mirroring the AES-SIV contract.
    struct Mock {
        key: u8,
    }

    impl Mock {
        fn mac(&self, parts: &[&[u8]]) -> [u8; TAG_LEN] {
            let mut tag = [self.key; TAG_LEN];
            let mut n = 0usize;
            for part in parts {
                for &b in part.iter() {
                    tag[n % TAG_LEN] = tag[n % TAG_LEN].rotate_left(3) ^ b ^ (n as u8);
                    n += 1;
                }
                tag[n % TAG_LEN] ^= 0xa5;
                n += 1;
            }
            tag
        }
    }

    impl V3Primitives for Mock {
        fn seal_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &mut [u8; TAG_LEN]) -> bool {
            *tag = self.mac(&[b"config", prefix]);
            true
        }
        fn open_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &[u8; TAG_LEN]) -> bool {
            self.mac(&[b"config", prefix]) == *tag
        }
        fn seal_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], plaintext: &[u8], out: &mut [u8]) -> bool {
            if out.len() != plaintext.len() + TAG_LEN {
                return false;
            }
            out[..TAG_LEN].copy_from_slice(&self.mac(&[b"file", config, path, plaintext]));
            for (o, p) in out[TAG_LEN..].iter_mut().zip(plaintext) {
                *o = p ^ self.key;
            }
            true
        }
        fn open_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], sealed: &[u8], out: &mut [u8]) -> bool {
            if sealed.len() < TAG_LEN || out.len() != sealed.len() - TAG_LEN {
                return false;
            }
            let plaintext: std::vec::Vec<u8> = sealed[TAG_LEN..].iter().map(|c| c ^ self.key).collect();
            if self.mac(&[b"file", config, path, &plaintext]) != sealed[..TAG_LEN] {
                return false;
            }
            out.copy_from_slice(&plaintext);
            true
        }
        fn config_id(&self, config: &[u8; CONFIG_LEN]) -> [u8; ID_LEN] {
            self.mac(&[b"id", config])
        }
    }

    fn seal(m: &Mock, config: &[u8; CONFIG_LEN], path: &[u8], pt: &[u8]) -> Result<std::vec::Vec<u8>, Refusal> {
        let mut out = std::vec![0u8; pt.len() + FILE_MIN_LEN];
        seal_record(m, config, path, pt, &mut out).map(|_| out)
    }

    fn open(m: &Mock, config: &[u8; CONFIG_LEN], path: &[u8], record: &[u8]) -> Result<std::vec::Vec<u8>, Refusal> {
        let mut out = std::vec![0u8; record.len().saturating_sub(FILE_MIN_LEN)];
        open_record(m, config, path, record, &mut out).map(|_| out)
    }

    #[test]
    fn canonical_path_policy() {
        for good in [b"a.secret".as_slice(), b"dir/x.secret", b"a b.secret", b".secret", b"d/.secret",
                     b"raw/\xff.secret", b"dir/new\nline.secret", b"...secret", b"a/.../b.secret",
                     b".env", b"config/production.yaml", b"private/key", b"x", b"x.secret.txt",
                     b"d/.transcrypt/config", b".transcrypt", b"a.gitattributes", b"d/.gitmodules",
                     b".gitattributes.d/x"] {
            assert!(is_canonical_protected_path(good), "rejected {:?}", good);
        }
        for bad in [b"".as_slice(), b"/root.secret", b"../bad.secret", b"x/../bad.secret",
                    b"./x.secret", b"x//y.secret", b"x/./y.secret", b"x.secret/", b"evil\0.secret",
                    b"x.secret/..", b"x.secret/.", b".transcrypt/config", b".transcrypt/x",
                    b".gitattributes", b"d/.gitattributes", b".gitmodules"] {
            assert!(!is_canonical_protected_path(bad), "accepted {:?}", bad);
        }
        let mut long = std::vec![b'x'; MAX_PATH];
        assert!(is_canonical_protected_path(&long));
        long.push(b'x');
        assert!(!is_canonical_protected_path(&long));
        assert!(is_reserved_path(b".transcrypt/") && !is_reserved_path(b".transcrypt"));
    }

    #[test]
    fn sealed_records_are_bound_to_config_and_path() {
        let m = Mock { key: 9 };
        let config = initialize_config(&m, &[3u8; SALT_LEN]).unwrap();
        assert!(authenticate_config(&m, &config).is_ok());
        assert_eq!(authenticate_config(&Mock { key: 10 }, &config), Err(Refusal::ConfigAuthentication));
        let mut bad = config;
        bad[0] ^= 1;
        assert_eq!(authenticate_config(&m, &bad), Err(Refusal::Config));
        for pt in [b"".as_slice(), b"hello", &[0u8, 1, 255]] {
            let rec = seal(&m, &config, b"v/a.secret", pt).unwrap();
            assert_eq!(&rec[..FILE_HEADER_LEN], &encode_file_header(&m.config_id(&config)));
            assert_eq!(open(&m, &config, b"v/a.secret", &rec).unwrap(), pt);
            assert_eq!(open(&m, &config, b"v/b.secret", &rec), Err(Refusal::Authentication));
            let mut flipped = rec.clone();
            *flipped.last_mut().unwrap() ^= 1;
            assert!(open(&m, &config, b"v/a.secret", &flipped).is_err());
            assert_eq!(seal(&m, &config, b"v/a.secret", &rec), Err(Refusal::DoubleEncryption));
            assert_eq!(seal(&m, &config, b"../a.secret", pt), Err(Refusal::Path));
            assert_eq!(open(&m, &config, b".gitattributes", &rec), Err(Refusal::Path));
        }
        let other = initialize_config(&m, &[4u8; SALT_LEN]).unwrap();
        let rec = seal(&m, &config, b"a.secret", b"x").unwrap();
        assert_eq!(open(&m, &other, b"a.secret", &rec), Err(Refusal::ConfigMismatch));
        assert_eq!(open(&m, &config, b"a.secret", &rec[..FILE_MIN_LEN - 1]), Err(Refusal::Envelope));
        let mut out = [0u8; 2];
        assert_eq!(open_record(&m, &config, b"a.secret", &rec, &mut out), Err(Refusal::Size));
        assert_eq!(seal_record(&m, &config, b"a.secret", b"x", &mut out), Err(Refusal::Size));
    }

    #[test]
    fn lifecycle_actions_never_discard_unknown_bytes() {
        let m = Mock { key: 1 };
        let config = initialize_config(&m, &[5u8; SALT_LEN]).unwrap();
        let rec = seal(&m, &config, b"a.secret", b"plain").unwrap();
        assert_eq!(hydrate_action(&rec, &rec, b"plain"), Ok(HydrateAction::Publish));
        assert_eq!(hydrate_action(b"plain", &rec, b"plain"), Ok(HydrateAction::Keep));
        assert_eq!(hydrate_action(b"edited", &rec, b"plain"), Err(Refusal::UnexpectedWorktree));
        assert_eq!(lock_action(&rec, &rec, b""), Ok(LockAction::Keep));
        let resealed = seal(&m, &config, b"a.secret", b"plain").unwrap();
        assert_eq!(lock_action(b"plain", &rec, &resealed), Ok(LockAction::Flush));
        let resealed = seal(&m, &config, b"a.secret", b"edited").unwrap();
        assert_eq!(lock_action(b"edited", &rec, &resealed), Err(Refusal::UnexpectedWorktree));
    }

    #[test]
    fn agent_requests_are_authorized_against_the_active_config() {
        let a = [1u8; CONFIG_LEN];
        let mut b = a;
        b[54] = 2;
        assert_eq!(authorize_agent_request(b'P', &a, &a, b"", 0), Ok(AgentOp::Ping));
        assert_eq!(authorize_agent_request(b'X', &a, &a, b"", 0), Ok(AgentOp::Stop));
        assert_eq!(authorize_agent_request(b'E', &a, &a, b"x.secret", 9), Ok(AgentOp::Encrypt));
        assert_eq!(authorize_agent_request(b'D', &a, &a, b"x.secret", 0), Ok(AgentOp::Decrypt));
        assert_eq!(authorize_agent_request(b'D', &b, &a, b"x.secret", 0), Err(Refusal::ConfigMismatch));
        assert_eq!(authorize_agent_request(b'E', &a, &a, b".transcrypt/config", 0), Err(Refusal::Path));
        assert_eq!(authorize_agent_request(b'P', &a, &a, b"x.secret", 0), Err(Refusal::Request));
        assert_eq!(authorize_agent_request(b'X', &a, &a, b"", 1), Err(Refusal::Request));
        assert_eq!(authorize_agent_request(b'Q', &a, &a, b"", 0), Err(Refusal::Request));
        assert_eq!(authorize_agent_request(b'E', &a, &a, b"x.secret", MAX_RECORD + 1), Err(Refusal::Size));
    }

    #[test]
    fn attr_records_name_the_requested_path_and_its_filter() {
        let response = b"a.secret\0filter\0transcrypt-v3\0d/b c\0filter\0unspecified\0e\0filter\0transcrypt-v3x\0";
        let first = parse_attr_record(response, 0, b"a.secret").unwrap();
        assert!(first.protected);
        let second = parse_attr_record(response, first.next, b"d/b c").unwrap();
        assert!(!second.protected);
        let third = parse_attr_record(response, second.next, b"e").unwrap();
        assert!(!third.protected);
        assert_eq!(third.next, response.len());
        assert_eq!(parse_attr_record(response, third.next, b""), Err(Refusal::Attribute));
        // Another path, another attribute, a truncated record, a start beyond the end.
        assert_eq!(parse_attr_record(response, 0, b"a.secreT"), Err(Refusal::Attribute));
        assert_eq!(parse_attr_record(response, 0, b"a"), Err(Refusal::Attribute));
        assert_eq!(parse_attr_record(b"a\0diff\0transcrypt-v3\0", 0, b"a"), Err(Refusal::Attribute));
        assert_eq!(parse_attr_record(b"a\0filter\0transcrypt-v3", 0, b"a"), Err(Refusal::Attribute));
        assert_eq!(parse_attr_record(response, response.len() + 1, b""), Err(Refusal::Attribute));
        // A path containing what looks like a record separator still must match exactly.
        let tricky = b"x\0filter\0transcrypt-v3\0";
        assert!(parse_attr_record(tricky, 0, b"x").unwrap().protected);
        assert_eq!(parse_attr_record(tricky, 0, b"x\0filter"), Err(Refusal::Attribute));
    }

    #[test]
    fn attr_responses_must_answer_every_path_in_order() {
        let request = b"a.secret\0d/b c\0e\0";
        let response = b"a.secret\0filter\0transcrypt-v3\0d/b c\0filter\0unspecified\0e\0filter\0transcrypt-v3\0";
        let mut flags = [false; 3];
        assert!(parse_attr_response(request, response, &mut flags));
        assert_eq!(flags, [true, false, true]);
        assert!(parse_attr_response(b"", b"", &mut []));
        assert!(!parse_attr_response(b"", b"x", &mut []));
        // Truncated, extended, reordered, too few or too many slots, unterminated request.
        assert!(!parse_attr_response(request, &response[..response.len() - 1], &mut flags));
        assert!(!parse_attr_response(request, &[&response[..], b"x"].concat(), &mut flags));
        assert!(!parse_attr_response(b"e\0a.secret\0d/b c\0", response, &mut flags));
        assert!(!parse_attr_response(request, response, &mut [false; 2]));
        assert!(!parse_attr_response(request, response, &mut [false; 4]));
        assert!(!parse_attr_response(b"a.secret\0d/b c\0e", response, &mut flags));
    }

    #[test]
    fn smudge_keeps_only_records_and_opens_only_its_own_config() {
        let id = [7u8; ID_LEN];
        let mut record = std::vec::Vec::from(&encode_file_header(&id)[..]);
        record.extend_from_slice(&[0u8; TAG_LEN]);
        assert_eq!(smudge_action(&record, &id, true), Ok(SmudgeAction::Open));
        assert_eq!(smudge_action(&record, &id, false), Ok(SmudgeAction::Keep));
        assert_eq!(smudge_action(&record, &[8u8; ID_LEN], true), Ok(SmudgeAction::Keep));
        assert_eq!(smudge_action(b"plaintext that bypassed the filter", &id, true), Err(Refusal::Foreign));
        assert_eq!(smudge_action(b"", &id, false), Err(Refusal::Foreign));
        assert_eq!(smudge_action(&std::vec![0u8; MAX_RECORD + 1], &id, true), Err(Refusal::Size));
    }

    #[test]
    fn index_entries_are_parsed_at_the_first_tab_and_stage_zero_only() {
        let oid = b"0123456789abcdef0123456789abcdef01234567";
        let mut e = std::vec::Vec::new();
        e.extend_from_slice(b"100644 ");
        e.extend_from_slice(oid);
        e.extend_from_slice(b" 0\tdir/a\tb.secret");
        let parsed = parse_index_entry(&e).unwrap();
        assert!(parsed.regular);
        assert_eq!(&e[parsed.path_start..], b"dir/a\tb.secret");
        let exec: std::vec::Vec<u8> = [b"100755 ".as_slice(), oid, b" 0\tx.secret"].concat();
        assert!(parse_index_entry(&exec).unwrap().regular);
        let group: std::vec::Vec<u8> = [b"100664 ".as_slice(), oid, b" 0\tx.secret"].concat();
        assert!(!parse_index_entry(&group).unwrap().regular);
        let link: std::vec::Vec<u8> = [b"120000 ".as_slice(), oid, b" 0\tx.secret"].concat();
        assert!(!parse_index_entry(&link).unwrap().regular);
        for bad in [
            [b"100644 ".as_slice(), oid, b" 1\tx.secret"].concat(),  // unmerged
            [b"100644 ".as_slice(), oid, b" 0\t"].concat(),          // empty path
            [b"100644 ".as_slice(), oid, b" 0 x.secret"].concat(),    // no tab
            b"100644 0\tx".to_vec(),                                  // missing object id
            [b"1006440".as_slice(), oid, b" 0\tx.secret"].concat(),  // no separator
            std::vec::Vec::new(),
        ] {
            assert_eq!(parse_index_entry(&bad), Err(Refusal::Index), "{bad:?}");
        }
    }

    #[test]
    fn object_ids_and_record_envelopes() {
        assert!(is_object_id(&[b'0'; 40]));
        assert!(is_object_id(&[b'f'; 64]));
        for bad in [&b""[..], &[b'0'; 39], &[b'0'; 41], &[b'0'; 63], &[b'A'; 40], &[b'g'; 40], b"-0000000000000000000000000000000000000000"] {
            assert!(!is_object_id(bad), "{bad:?}");
        }
        let mut colon = [b'0'; 40];
        colon[1] = b':';
        assert!(!is_object_id(&colon));
        let id = core::array::from_fn(|i| i as u8);
        let header = encode_file_header(&id);
        let mut record = std::vec::Vec::from(&header[..]);
        record.extend_from_slice(&[0u8; TAG_LEN]);
        assert!(record_envelope_ok(&record, &id));
        assert!(!record_envelope_ok(&record[..FILE_MIN_LEN - 1], &id));
        let mut other = id;
        other[0] ^= 1;
        assert!(!record_envelope_ok(&record, &other));
        record[0] ^= 1;
        assert!(!record_envelope_ok(&record, &id));
        assert!(!record_envelope_ok(b"plaintext that is long enough to pass the size bound", &id));
    }

    #[test]
    fn envelope_prefix_refuses_impossible_sizes() {
        let id = core::array::from_fn(|i| i as u8);
        let header = encode_file_header(&id);
        let mut prefix = std::vec::Vec::from(&header[..]);
        prefix.extend_from_slice(&[0u8; TAG_LEN]);
        assert_eq!(prefix.len(), ENVELOPE_PREFIX_LEN);
        assert!(record_envelope_prefix_ok(FILE_MIN_LEN, &prefix, &id));
        assert!(record_envelope_prefix_ok(MAX_RECORD, &prefix, &id));
        // A declared size too small to hold a record, whatever the prefix.
        for size in [0, 1, FILE_HEADER_LEN, FILE_MIN_LEN - 1] {
            assert!(!record_envelope_prefix_ok(size, &prefix, &id), "{size}");
        }
        assert!(!record_envelope_prefix_ok(MAX_RECORD + 1, &prefix, &id));
        assert!(!record_envelope_prefix_ok(usize::MAX, &prefix, &id));
        // A prefix longer than the declared size.
        let mut longer = prefix.clone();
        longer.push(0);
        assert!(record_envelope_prefix_ok(FILE_MIN_LEN + 1, &longer, &id));
        assert!(!record_envelope_prefix_ok(FILE_MIN_LEN, &longer, &id));
        // A prefix shorter than `ENVELOPE_PREFIX_LEN` cannot show the envelope.
        assert!(!record_envelope_prefix_ok(FILE_MIN_LEN, &prefix[..FILE_MIN_LEN - 1], &id));
    }

    #[test]
    fn envelope_prefix_decides_as_the_whole_record() {
        let id = core::array::from_fn(|i| i as u8);
        let mut other = id;
        other[0] ^= 1;
        let header = encode_file_header(&id);
        let mut bad_magic = header;
        bad_magic[0] ^= 1;
        let sizes = [0, FILE_HEADER_LEN, FILE_MIN_LEN - 1, FILE_MIN_LEN, FILE_MIN_LEN + 1, MAX_RECORD, MAX_RECORD + 1];
        for start in [&header[..], &bad_magic[..], b"plaintext"] {
            for size in sizes {
                let mut record = std::vec::Vec::from(&start[..start.len().min(size)]);
                record.resize(size, 0);
                let prefix = &record[..size.min(ENVELOPE_PREFIX_LEN)];
                for want in [&id, &other] {
                    let whole = record_envelope_ok(&record, want);
                    assert_eq!(record_envelope_prefix_ok(size, prefix, want), whole, "{size} {start:?}");
                    assert_eq!(whole, start == &header[..] && want == &id && (FILE_MIN_LEN..=MAX_RECORD).contains(&size));
                }
            }
        }
    }

    #[test]
    fn only_local_changes_are_repaired() {
        use SealAction::*;
        for (opens, local, envelope, moved, expected) in [
            (true, true, true, true, Keep), (true, false, false, false, Keep),
            (false, false, false, false, Leave), (false, false, true, true, Leave),
            (false, true, false, false, Seal), (false, true, false, true, Seal),
            (false, true, true, true, Rebind), (false, true, true, false, Leave),
        ] {
            assert_eq!(seal_action(opens, local, envelope, moved), expected);
        }
    }

    #[test]
    fn keyless_or_settled_entries_check_the_envelope() {
        use EntryCheck::*;
        for (keyed, incremental, settled, expected) in [
            (true, false, false, Authenticate), (true, false, true, Authenticate),
            (true, true, false, Authenticate), (true, true, true, Envelope),
            (false, false, false, EnvelopeNotMoved), (false, false, true, Envelope),
            (false, true, false, EnvelopeNotMoved), (false, true, true, Envelope),
        ] {
            assert_eq!(entry_check(keyed, incremental, settled), expected);
        }
    }

    #[test]
    fn object_ids_start_after_the_mode() {
        assert_eq!(OID_START, REGULAR_MODE.len() + 1);
        assert_eq!(OID_START, EXECUTABLE_MODE.len() + 1);
        assert_eq!(OID_START, MODE_LEN + 1);
        assert_eq!(OID_END_LEN, OID_END.len());
        assert_eq!(ENTRY_FIXED_LEN, OID_START + OID_END_LEN);
    }

    #[test]
    fn pkt_line_lengths() {
        assert_eq!(decode_pkt_len(b"0000"), Ok(0));
        assert_eq!(decode_pkt_len(b"0005"), Ok(5));
        assert_eq!(decode_pkt_len(b"00ff"), Ok(255));
        assert_eq!(decode_pkt_len(b"fff0"), Ok(MAX_PKT_LEN));
        for bad in [b"0001", b"0004", b"fff1", b"ffff", b"00FF", b"00g0", b" 005", b"-005"] {
            assert_eq!(decode_pkt_len(bad), Err(Refusal::Request), "{bad:?}");
        }
    }

    #[test]
    fn agent_frames_roundtrip() {
        let config = core::array::from_fn(|i| (i * 7) as u8);
        for len in [0u32, 1, 255, 256, 4096, 0x0102_0304, u32::MAX] {
            let h = encode_frame_header(b'D', &config, len);
            assert_eq!(decode_frame_header(&h), FrameHeader { opcode: b'D', config, path_len: len });
            assert_eq!(&h[1 + CONFIG_LEN..], &len.to_be_bytes());
            assert_eq!(decode_be_u32(&encode_be_u32(len)), len);
        }
    }

    /// The bytes of a listing of `(mode, oid digit, path)` records.
    fn listing_bytes(records: &[(&str, u8, &[u8])]) -> std::vec::Vec<u8> {
        let mut bytes = std::vec::Vec::new();
        for (mode, digit, path) in records {
            bytes.extend_from_slice(mode.as_bytes());
            bytes.push(b' ');
            bytes.extend_from_slice(&[*digit; 40]);
            bytes.extend_from_slice(b" 0\t");
            bytes.extend_from_slice(path);
            bytes.push(0);
        }
        bytes
    }

    type Listing = (std::vec::Vec<u8>, std::vec::Vec<usize>);

    /// A listing with unique paths in byte order, and its `ends`.
    fn listing(records: &[(&str, u8, &[u8])]) -> Listing {
        let bytes = listing_bytes(records);
        let mut ends = std::vec![0; records.len()];
        assert!(parse_listing(&bytes, &mut ends, true));
        (bytes, ends)
    }

    /// The object order of a listing (by object id, then position).
    fn order(l: &Listing) -> std::vec::Vec<usize> {
        let id = |j: usize| listing_fields(&l.0, &l.1, j).map(|f| l.0[f.start + OID_START..f.oid_end].to_vec()).unwrap();
        let mut order: std::vec::Vec<usize> = (0..l.1.len()).collect();
        order.sort_by_key(|j| (id(*j), *j));
        assert!(object_order_ok(&l.0, &l.1, &order));
        order
    }

    fn held(index: &Listing, other: &Listing) -> std::vec::Vec<bool> {
        let mut out = std::vec![true; index.1.len()];
        let wanted = std::vec![true; index.1.len()];
        assert!(held_entries(&index.0, &index.1, &wanted, &other.0, &other.1, &mut out));
        out
    }

    fn elsewhere(index: &Listing, i: usize, head: &Listing, parent: &Listing) -> bool {
        blob_elsewhere(&index.0, &index.1, &order(index), i, &head.0, &head.1, &order(head), &parent.0, &parent.1,
            &order(parent))
    }

    fn source(index: &Listing, i: usize, head: &Listing, from: usize) -> usize {
        next_move_source(&index.0, &index.1, i, &head.0, &head.1, &order(head), from)
    }

    #[test]
    fn listings_are_parsed_exactly() {
        let (bytes, ends) = listing(&[("100644", b'a', b"x\ty"), ("120000", b'b', b"y/l")]);
        let first = listing_fields(&bytes, &ends, 0).unwrap();
        assert_eq!(&bytes[first.start + OID_START..first.oid_end], &[b'a'; 40]);
        assert_eq!(&bytes[first.path_start..first.end], b"x\ty");
        assert!(first.regular);
        let second = listing_fields(&bytes, &ends, 1).unwrap();
        assert_eq!(&bytes[second.path_start..second.end], b"y/l");
        assert!(!second.regular);
        assert_eq!(listing_fields(&bytes, &ends, 2), None);
        assert!(parse_listing(b"", &mut [], true));
        // Wrong count, truncated, extended, unmerged, bad object id, empty record.
        assert!(!parse_listing(&bytes, &mut [0; 1], true));
        assert!(!parse_listing(&bytes, &mut [0; 3], true));
        assert!(!parse_listing(&bytes[..bytes.len() - 1], &mut [0; 2], true));
        assert!(!parse_listing(&[&bytes[..], b"\0"].concat(), &mut [0; 2], true));
        let unmerged = [b"100644 ".as_slice(), &[b'a'; 40], b" 1\tx\0"].concat();
        assert!(!parse_listing(&unmerged, &mut [0; 1], true));
        let short = [b"100644 ".as_slice(), &[b'a'; 39], b" 0\tx\0"].concat();
        assert!(!parse_listing(&short, &mut [0; 1], true));
        let upper = [b"100644 ".as_slice(), &[b'A'; 40], b" 0\tx\0"].concat();
        assert!(!parse_listing(&upper, &mut [0; 1], true));
        assert!(!parse_listing(b"\0", &mut [0; 1], true));
    }

    #[test]
    fn listings_are_in_path_order() {
        // Git's order is byte order of the whole path ("a-b" < "a.c" < "a/b" < "a0").
        for (a, b) in [(&b"a"[..], &b"b"[..]), (b"a", b"ab"), (b"", b"a"), (b"a-b", b"a.c"), (b"a.c", b"a/b"),
            (b"a/b", b"a0"), (b"a/b/c", b"a/bc"), (b"z\x7f", b"z\x80"), (b"A", b"a")]
        {
            assert!(bytes_lt(a, b) && !bytes_lt(b, a), "{a:?} {b:?}");
        }
        assert!(!bytes_lt(b"", b"") && !bytes_lt(b"a/b", b"a/b"));
        let mut ends = [0; 2];
        let sorted = listing_bytes(&[("100644", b'1', b"a.c"), ("100644", b'2', b"a/b")]);
        assert!(parse_listing(&sorted, &mut ends, true));
        // Out of order or a path twice (a crafted tree): refused, unless
        // repeated paths are allowed (the merged incoming commits).
        let swapped = listing_bytes(&[("100644", b'2', b"a/b"), ("100644", b'1', b"a.c")]);
        assert!(!parse_listing(&swapped, &mut ends, true));
        assert!(!parse_listing(&swapped, &mut ends, false));
        let twice = listing_bytes(&[("100644", b'1', b"a.secret"), ("100644", b'2', b"a.secret")]);
        assert!(!parse_listing(&twice, &mut ends, true));
        assert!(parse_listing(&twice, &mut ends, false));
        // In a merged listing, every record at a path is found.
        let index = listing(&[("100644", b'2', b"a.secret")]);
        let other = (twice, ends.to_vec());
        assert_eq!(held(&index, &other), [true]);
    }

    #[test]
    fn object_orders_list_each_record_once_by_object_id() {
        let l = listing(&[("100644", b'2', b"a"), ("100644", b'1', b"b"), ("100644", b'2', b"c")]);
        assert_eq!(order(&l), [1, 0, 2]);
        for bad in [&[0usize, 1, 2][..], &[1, 2, 0], &[1, 0, 0], &[1, 0, 3], &[1, 0], &[1, 0, 2, 2]] {
            assert!(!object_order_ok(&l.0, &l.1, bad), "{bad:?}");
        }
        assert!(object_order_ok(b"", &[], &[]));
    }

    #[test]
    fn snapshot_queries_compare_object_and_path() {
        let index = listing(&[("100644", b'1', b"a"), ("100644", b'2', b"b"), ("100644", b'3', b"c"),
            ("100644", b'4', b"moved")]);
        let head = listing(&[("100644", b'1', b"a"), ("100755", b'2', b"b"), ("100644", b'9', b"c"),
            ("100644", b'4', b"kept"), ("100644", b'4', b"moved"), ("100644", b'4', b"old")]);
        // The mode does not matter; another blob at the path is not held.
        assert_eq!(held(&index, &head), [true, true, false, true]);
        assert_eq!(held(&head, &index), [true, true, false, false, true, false]);
        let mut out = [true; 4];
        assert!(held_entries(&index.0, &index.1, &[false, true, true, false], &head.0, &head.1, &mut out));
        assert_eq!(out, [false, true, false, false]);
        assert!(!held_entries(&index.0, &index.1, &[true; 3], &head.0, &head.1, &mut out));
        let empty = listing(&[]);
        assert_eq!(held(&index, &empty), [false; 4]);
        // Move sources of `moved` (entry 3): the HEAD paths of its blob that
        // left the index, in HEAD order, never its own path.
        assert_eq!(source(&index, 3, &head, 0), 3);
        assert_eq!(source(&index, 3, &head, 4), 5);
        assert_eq!(source(&index, 3, &head, 6), 6);
        assert_eq!(source(&index, 0, &head, 0), 6);
        let kept = listing(&[("100644", b'4', b"kept"), ("100644", b'4', b"moved")]);
        assert_eq!(source(&kept, 1, &head, 0), 5);
        assert!(elsewhere(&index, 3, &empty, &head));
        assert!(!elsewhere(&index, 0, &head, &head));
        assert!(elsewhere(&kept, 1, &empty, &empty));
        // `local_change`: changed and known not to come from a commit, or forced plaintext.
        for (in_head, known, in_incoming, forced, envelope, expected) in [
            (false, true, false, false, true, true), (true, true, false, false, false, false),
            (false, false, false, false, true, false), (false, true, true, false, false, false),
            (true, true, true, true, false, true), (true, true, true, true, true, false),
        ] {
            assert_eq!(is_local_change(in_head, known, in_incoming, forced, envelope), expected);
        }
    }

    /// The queries agree with their definitions on random listings: held
    /// (`Holds`), the keyless move check (`BlobElsewhere`) and move sources
    /// (`MoveSource`, first from an offset).
    #[test]
    fn snapshot_queries_match_their_definitions() {
        let mut state = 0x2545_f491_4f6c_dd1du64;
        let mut next = move |n: u64| { state ^= state << 13; state ^= state >> 7; state ^= state << 17; state % n };
        let names: [&[u8]; 8] = [b"a", b"a-b", b"a.c", b"a/b", b"a/b/c", b"a0", b"b", b"b\xc3\xa9"];
        for _ in 0..300 {
            let mut random = |size: u64| {
                let mut records: std::vec::Vec<(&str, u8, &[u8])> = std::vec::Vec::new();
                for name in names {
                    if next(8) < size {
                        records.push(("100644", b'0' + next(4) as u8, name));
                    }
                }
                listing(&records)
            };
            let (index, head, parent) = (random(6), random(5), random(3));
            let entries = |l: &Listing| (0..l.1.len()).map(|j| {
                let f = listing_fields(&l.0, &l.1, j).unwrap();
                (l.0[f.start + OID_START..f.oid_end].to_vec(), l.0[f.path_start..f.end].to_vec())
            }).collect::<std::vec::Vec<_>>();
            let (es, hs, ps) = (entries(&index), entries(&head), entries(&parent));
            let holds = |l: &[(std::vec::Vec<u8>, std::vec::Vec<u8>)], e: &(std::vec::Vec<u8>, std::vec::Vec<u8>)| l.contains(e);
            let expected: std::vec::Vec<bool> = es.iter().map(|e| holds(&hs, e)).collect();
            assert_eq!(held(&index, &head), expected);
            for (i, e) in es.iter().enumerate() {
                let other = |l: &[(std::vec::Vec<u8>, std::vec::Vec<u8>)]| l.iter().any(|x| x.0 == e.0 && x.1 != e.1);
                assert_eq!(elsewhere(&index, i, &head, &parent), other(&es) || other(&hs) || other(&ps));
                for from in 0..=hs.len() {
                    let first = (from..hs.len()).find(|j| hs[*j].0 == e.0 && hs[*j].1 != e.1 && !holds(&es, &hs[*j]));
                    assert_eq!(source(&index, i, &head, from), first.unwrap_or(hs.len()));
                }
            }
        }
    }

    /// Lookups stay fast on large listings where nothing matches (a whole
    /// directory rewritten): every query is a binary search, not a scan.
    #[test]
    fn snapshot_queries_scale_to_large_listings() {
        let n = 50_000;
        let names: std::vec::Vec<std::vec::Vec<u8>> = (0..n).map(|i| std::format!("d/f{i:06}").into_bytes()).collect();
        let build = |digit: u8| {
            let records: std::vec::Vec<(&str, u8, &[u8])> = names.iter().map(|p| ("100644", digit, p.as_slice())).collect();
            listing(&records)
        };
        let (index, head) = (build(b'1'), build(b'2'));
        let (index_order, head_order) = (order(&index), order(&head));
        let started = std::time::Instant::now();
        assert!(held(&index, &head).iter().all(|h| !h));
        for i in (0..n).step_by(7) {
            assert!(blob_elsewhere(&index.0, &index.1, &index_order, i, &head.0, &head.1, &head_order, &head.0,
                &head.1, &head_order));
            assert_eq!(next_move_source(&index.0, &index.1, i, &head.0, &head.1, &head_order, 0), n);
        }
        // Quadratic lookups take minutes here.
        assert!(started.elapsed() < std::time::Duration::from_secs(20), "{:?}", started.elapsed());
    }

    #[test]
    fn listing_attributes_and_selectability() {
        let (bytes, ends) = listing(&[("100644", b'c', b".gitattributes"), ("100644", b'a', b"a.env"),
            ("120000", b'b', b"link"), ("100755", b'd', b"run")]);
        let response = b".gitattributes\0filter\0unset\0a.env\0filter\0transcrypt-v3\0link\0filter\0unspecified\0run\0filter\0transcrypt-v3\0";
        let mut flags = [false; 4];
        assert!(parse_listing_attrs(&bytes, &ends, response, &mut flags));
        assert_eq!(flags, [false, true, false, true]);
        assert_eq!(first_unselectable(&bytes, &ends, &flags), 4);
        assert_eq!(first_unselectable(&bytes, &ends, &[false, true, true, true]), 2);
        assert_eq!(first_unselectable(&bytes, &ends, &[true, false, false, false]), 0);
        assert!(!parse_listing_attrs(&bytes, &ends, &response[..response.len() - 1], &mut flags));
        assert!(!parse_listing_attrs(&bytes, &ends, &[&response[..], b"x"].concat(), &mut flags));
        assert!(!parse_listing_attrs(&bytes, &ends, response, &mut [false; 3]));
        let swapped = b"a.env\0filter\0transcrypt-v3\0.gitattributes\0filter\0unset\0link\0filter\0unspecified\0run\0filter\0transcrypt-v3\0";
        assert!(!parse_listing_attrs(&bytes, &ends, swapped, &mut flags));
    }

    #[test]
    fn stored_keys_unlock_only_their_own_authentic_config() {
        let config = [7u8; CONFIG_LEN];
        let mut file = std::vec::Vec::from(&config[..]);
        file.extend_from_slice(&[1u8; KEY_LEN]);
        assert_eq!(stored_key_state(true, &file, &config, true), StoredKey::Unlocked);
        assert_eq!(stored_key_state(true, &file, &config, false), StoredKey::Stale);
        let mut other = config;
        other[54] = 8;
        assert_eq!(stored_key_state(true, &file, &other, true), StoredKey::Stale);
        assert_eq!(stored_key_state(false, &file, &config, true), StoredKey::Absent);
        assert_eq!(stored_key_state(true, &[1u8; KEY_LEN], &config, true), StoredKey::Absent);
        for n in [0, 1, KEY_LEN + 1, KEY_FILE_LEN - 1, KEY_FILE_LEN + 1] {
            assert_eq!(stored_key_state(true, &std::vec![0u8; n], &config, true), StoredKey::Damaged, "{n}");
        }
    }

    #[test]
    fn batch_headers_name_the_object_and_a_canonical_size() {
        let oid = b"0123456789abcdef0123456789abcdef01234567";
        let header = |rest: &str| [oid.as_slice(), rest.as_bytes()].concat();
        assert_eq!(parse_batch_header(&header(" blob 12\n"), oid), Some(12));
        assert_eq!(parse_batch_header(&header(" blob 0\n"), oid), Some(0));
        assert_eq!(parse_batch_header(&header(" blob 9999999999999999999\n"), oid), Some(9_999_999_999_999_999_999));
        for bad in [" blob 012\n", " blob 00\n", " blob +12\n", " blob 12", " blob \n", " tree 12\n", " missing\n",
                    " blob 1 2\n", " blob 12\n\n", " blob 10000000000000000000\n", "  blob 12\n"] {
            assert_eq!(parse_batch_header(&header(bad), oid), None, "{bad:?}");
        }
        let mut other = *oid;
        other[0] = b'f';
        assert_eq!(parse_batch_header(&header(" blob 12\n"), &other), None);
        assert_eq!(parse_batch_header(b"", oid), None);
        assert_eq!(blob_read(MAX_RECORD as u64, false), BlobRead::Read);
        assert_eq!(blob_read(MAX_RECORD as u64 + 1, true), BlobRead::Skip);
        assert_eq!(blob_read(u64::MAX, false), BlobRead::TooLarge);
    }
}
