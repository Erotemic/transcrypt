#![no_std]
//! Pure, dependency-free Transcrypt v3 wire grammar. Crypto lives in the adapter.
//! No legacy format recognition, format guessing, or plaintext fallback.

pub const CONFIG_MAGIC: [u8; 7] = *b"TCFG3\0\x01";
pub const FILE_MAGIC: [u8; 6] = *b"TV3F\0\x01";
pub const SALT_LEN: usize = 32;
pub const TAG_LEN: usize = 16;
pub const ID_LEN: usize = 16;
pub const CONFIG_PREFIX_LEN: usize = 39;
pub const CONFIG_LEN: usize = 55;
pub const FILE_HEADER_LEN: usize = 22;
pub const FILE_MIN_LEN: usize = FILE_HEADER_LEN + TAG_LEN;

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

/// Decode the fixed-size committed config record. This is the primary pure
/// codec entrypoint for Charon/Aeneas: no dynamically-sized slice operations,
/// filesystem state, allocation, or external cryptographic library calls.
/// Authentication is a separate operation performed by the cryptographic
/// adapter *after* this structural parse.
pub fn decode_config_exact(input: &[u8; CONFIG_LEN]) -> Result<Config, FormatError> {
    let mut i = 0;
    while i < CONFIG_MAGIC.len() {
        if input[i] != CONFIG_MAGIC[i] {
            return Err(FormatError::Magic);
        }
        i += 1;
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
/// This public slice boundary delegates the content decision to the *same*
/// fixed-size decoder targeted by formal refinement.
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

/// Decode a fixed-width file header. This is the second pure refinement
/// target; it is also used by the production slice-based parser below.
/// The caller is responsible for checking that at least TAG_LEN body bytes
/// follow the header and for authenticating the complete file record.
pub fn decode_file_header_exact(input: &[u8; FILE_HEADER_LEN]) -> Result<[u8; ID_LEN], FormatError> {
    let mut i = 0;
    while i < FILE_MAGIC.len() {
        if input[i] != FILE_MAGIC[i] {
            return Err(FormatError::Magic);
        }
        i += 1;
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
// Everything below is also extracted by Charon/Aeneas. The effectful adapter
// (`transcrypt-v3`) supplies cryptographic primitives through `V3Primitives`
// and performs Git/filesystem I/O; every *decision* about whether bytes may
// be sealed, released, published or flushed is made here, so the adapter
// cannot skip a gate. Loops are plain bounded `while` loops for extraction.
// ---------------------------------------------------------------------------

/// Largest plaintext accepted by any v3 operation (16 MiB).
pub const MAX_FILE: usize = 16 * 1024 * 1024;
/// Largest canonical Git-relative pathname accepted as associated data.
pub const MAX_PATH: usize = 4096;
/// Largest record or agent body: a maximal plaintext plus its envelope.
pub const MAX_RECORD: usize = MAX_FILE + FILE_MIN_LEN;
/// Protected Git paths are exactly those ending in this suffix.
pub const PROTECTED_SUFFIX: [u8; 7] = *b".secret";
/// Git `check-attr -z` output following each path: `NUL filter NUL transcrypt-v3 NUL`.
pub const FILTER_ATTR_SUFFIX: [u8; 22] = *b"\0filter\0transcrypt-v3\0";

/// Every reason the protocol core refuses an operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// Path is not a canonical protected Git-relative pathname.
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

/// A Git path is protected iff it ends in `.secret`. Because the suffix has
/// no `/`, this is the same as the basename ending in `.secret`, which is
/// also what Git's `*.secret` attribute pattern matches.
pub fn is_protected_path(path: &[u8]) -> bool {
    let n = path.len();
    if n < PROTECTED_SUFFIX.len() {
        return false;
    }
    let start = n - PROTECTED_SUFFIX.len();
    let mut k = 0;
    while k < PROTECTED_SUFFIX.len() {
        if path[start + k] != PROTECTED_SUFFIX[k] {
            return false;
        }
        k += 1;
    }
    true
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
/// absolute paths, duplicate or trailing separators), and protected. Raw
/// bytes are authoritative; there is no Unicode or filesystem normalization.
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
        } else if path[i] == 0 {
            ok = false;
        }
        i += 1;
    }
    ok && is_protected_path(path)
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

/// Whether `response[j..]` starts with `FILTER_ATTR_SUFFIX`.
fn filter_suffix_at(response: &[u8], j: usize) -> bool {
    if response.len() < j || response.len() - j < FILTER_ATTR_SUFFIX.len() {
        return false;
    }
    let mut k = 0;
    while k < FILTER_ATTR_SUFFIX.len() {
        if response[j + k] != FILTER_ATTR_SUFFIX[k] {
            return false;
        }
        k += 1;
    }
    true
}

/// Check Git's `check-attr --cached -z --stdin filter` response. `request`
/// is the exact stdin sent to Git: each path followed by one NUL. The
/// response is accepted iff it is the request with every NUL replaced by
/// `FILTER_ATTR_SUFFIX`, i.e. every requested path, in order, reports
/// `filter: transcrypt-v3` and nothing else is reported.
pub fn check_attr_response_ok(request: &[u8], response: &[u8]) -> bool {
    let mut ok = true;
    let mut i = 0;
    let mut j = 0;
    while ok && i < request.len() {
        if request[i] == 0 {
            if filter_suffix_at(response, j) {
                j += FILTER_ATTR_SUFFIX.len();
            } else {
                ok = false;
            }
        } else if j < response.len() && response[j] == request[i] {
            j += 1;
        } else {
            ok = false;
        }
        i += 1;
    }
    ok && j == response.len()
}

/// Length of a credential-agent request header: opcode, the 55-byte public
/// config and the big-endian path length. The path and a big-endian body
/// length follow (local IPC only, not part of the committed wire format).
pub const FRAME_HEADER_LEN: usize = 1 + CONFIG_LEN + 4;

/// Encode an agent request header.
pub fn encode_frame_header(opcode: u8, config: &[u8; CONFIG_LEN], path_len: u32) -> [u8; FRAME_HEADER_LEN] {
    let mut out = [0u8; FRAME_HEADER_LEN];
    out[0] = opcode;
    let mut i = 0;
    while i < CONFIG_LEN {
        out[1 + i] = config[i];
        i += 1;
    }
    let len = encode_be_u32(path_len);
    let mut k = 0;
    while k < 4 {
        out[1 + CONFIG_LEN + k] = len[k];
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
        config[i] = input[1 + i];
        i += 1;
    }
    let len = [input[1 + CONFIG_LEN], input[2 + CONFIG_LEN], input[3 + CONFIG_LEN], input[4 + CONFIG_LEN]];
    FrameHeader { opcode: input[0], config, path_len: decode_be_u32(&len) }
}

/// Big-endian `u32` encoding used for agent frame lengths.
pub fn encode_be_u32(x: u32) -> [u8; 4] {
    [(x >> 24) as u8, (x >> 16) as u8, (x >> 8) as u8, x as u8]
}

pub fn decode_be_u32(b: &[u8; 4]) -> u32 {
    ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32)
}

/// Git mode of a regular, non-executable file.
pub const REGULAR_MODE: [u8; 6] = *b"100644";

/// One parsed `git ls-files --stage -z` record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IndexEntry {
    /// The mode is exactly `100644`.
    pub regular: bool,
    /// The path is `entry[path_start..]`: everything after the first TAB.
    pub path_start: usize,
}

/// Parse a stage-0 record `<6-byte mode> SP <object id> SP 0 TAB <path>`.
/// The path, which becomes AES-SIV associated data, is everything after the
/// *first* TAB (Git paths may themselves contain TABs; modes and object ids
/// cannot). Unmerged entries (stage 1-3) and malformed records are refused.
pub fn parse_index_entry(entry: &[u8]) -> Result<IndexEntry, Refusal> {
    let n = entry.len();
    let mut t = 0;
    let mut found = false;
    while !found && t < n {
        if entry[t] == b'\t' {
            found = true;
        } else {
            t += 1;
        }
    }
    if !found || t < 10 || t + 1 >= n {
        return Err(Refusal::Index);
    }
    if entry[6] != b' ' || entry[t - 2] != b' ' || entry[t - 1] != b'0' {
        return Err(Refusal::Index);
    }
    let mut regular = true;
    let mut k = 0;
    while k < REGULAR_MODE.len() {
        if entry[k] != REGULAR_MODE[k] {
            regular = false;
        }
        k += 1;
    }
    Ok(IndexEntry { regular, path_start: t + 1 })
}

/// A Git object name as printed by `ls-files --stage` or `ls-tree`: 40
/// (SHA-1) or 64 (SHA-256) lowercase hexadecimal digits. The adapter passes
/// only such names to `git cat-file`, never revision syntax such as
/// `:<stage>:<path>` or text that Git could read as an option.
pub fn is_object_id(oid: &[u8]) -> bool {
    let n = oid.len();
    let mut ok = false;
    if n == 40 || n == 64 {
        ok = true;
    }
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
    if record.len() < FILE_MIN_LEN || record.len() > MAX_RECORD {
        return false;
    }
    match parse_file_header(record) {
        Ok(found) => bytes_eq(&found, id),
        Err(_) => false,
    }
}

/// Largest pkt-line Git sends or accepts: 4 length digits plus 65516 data bytes.
pub const MAX_PKT_LEN: usize = 65520;

/// Decode the 4-byte header of a pkt-line in Git's long-running filter
/// protocol: lowercase hexadecimal total length (header included). `Ok(0)`
/// is a flush packet; otherwise the length is between 5 and `MAX_PKT_LEN`.
/// Lengths 1 to 4 (special or empty packets, which the filter protocol never
/// uses), uppercase or other digits, and oversized lengths are refused.
pub fn decode_pkt_len(header: &[u8; 4]) -> Result<usize, Refusal> {
    let mut value = 0;
    let mut ok = true;
    let mut i = 0;
    while ok && i < 4 {
        let c = header[i];
        if c >= b'0' && c <= b'9' {
            value = value * 16 + (c - b'0') as usize;
        } else if c >= b'a' && c <= b'f' {
            value = value * 16 + (c - b'a' + 10) as usize;
        } else {
            ok = false;
        }
        i += 1;
    }
    if !ok || (value != 0 && value <= 4) || value > MAX_PKT_LEN {
        return Err(Refusal::Request);
    }
    Ok(value)
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_decoders_are_the_actual_public_parser_path() {
        let salt = core::array::from_fn(|i| i as u8);
        let tag = core::array::from_fn(|i| (255 - i) as u8);
        let config = Config { salt, tag };
        let bytes = encode_config(&config);
        assert_eq!(decode_config_exact(&bytes), Ok(config));
        assert_eq!(parse_config(&bytes), decode_config_exact(&bytes));
        // Each byte of either version marker must be enforced, with no
        // exceptions for offsets 5 or 6 and no fallback to older formats.
        for pos in 0..CONFIG_MAGIC.len() {
            let mut modified = bytes;
            modified[pos] ^= 1;
            assert_eq!(decode_config_exact(&modified), Err(FormatError::Magic));
            assert_eq!(parse_config(&modified), Err(FormatError::Magic));
        }
        let id = core::array::from_fn(|i| (i * 11) as u8);
        let header = encode_file_header(&id);
        assert_eq!(decode_file_header_exact(&header), Ok(id));
        for n in [FILE_MIN_LEN, FILE_MIN_LEN + 1, FILE_MIN_LEN + 255] {
            let mut blob = header.to_vec();
            blob.resize(n, 0x7f);
            assert_eq!(parse_file_header(&blob), decode_file_header_exact(&header));
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

    #[test]
    fn config_roundtrip_and_strict_length() {
        let config = Config { salt: [0x5a; SALT_LEN], tag: [0x81; TAG_LEN] };
        let bytes = encode_config(&config);
        assert_eq!(parse_config(&bytes), Ok(config));
        for n in 0..CONFIG_LEN {
            assert!(parse_config(&bytes[..n]).is_err());
        }
        let mut bad = bytes.to_vec();
        bad[0] = 0;
        assert_eq!(parse_config(&bad), Err(FormatError::Magic));
        bad = bytes.to_vec();
        bad.push(1);
        assert_eq!(parse_config(&bad), Err(FormatError::Length));
    }

    #[test]
    fn file_header_roundtrip_and_strict_magic() {
        let id = [0x41; ID_LEN];
        let mut record = encode_file_header(&id).to_vec();
        record.extend_from_slice(&[0x66; TAG_LEN]);
        assert_eq!(parse_file_header(&record), Ok(id));
        for n in 0..FILE_MIN_LEN {
            assert_eq!(parse_file_header(&record[..n]), Err(FormatError::Length));
        }
        record[2] = 0;
        assert_eq!(parse_file_header(&record), Err(FormatError::Magic));
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
                     b"raw/\xff.secret", b"dir/new\nline.secret", b"...secret", b"a/.../b.secret"] {
            assert!(is_canonical_protected_path(good), "rejected {:?}", good);
            assert!(is_protected_path(good));
        }
        for bad in [b"".as_slice(), b"absolute", b"/root.secret", b"../bad.secret", b"x/../bad.secret",
                    b"./x.secret", b"x//y.secret", b"x/./y.secret", b"x.secret/", b"evil\0.secret",
                    b"x.secret/..", b"x.secret/.", b"secret", b"x.secreT", b".secre"] {
            assert!(!is_canonical_protected_path(bad), "accepted {:?}", bad);
        }
        let mut long = std::vec![b'x'; MAX_PATH - 7];
        long.extend_from_slice(b".secret");
        assert!(is_canonical_protected_path(&long));
        long.insert(0, b'x');
        assert!(!is_canonical_protected_path(&long));
        assert!(is_protected_path(b"x/.secret") && !is_protected_path(b"x.secret.txt"));
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
            assert_eq!(open(&m, &config, b"v/a", &rec), Err(Refusal::Path));
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
        assert_eq!(authorize_agent_request(b'E', &a, &a, b"x", 0), Err(Refusal::Path));
        assert_eq!(authorize_agent_request(b'P', &a, &a, b"x.secret", 0), Err(Refusal::Request));
        assert_eq!(authorize_agent_request(b'X', &a, &a, b"", 1), Err(Refusal::Request));
        assert_eq!(authorize_agent_request(b'Q', &a, &a, b"", 0), Err(Refusal::Request));
        assert_eq!(authorize_agent_request(b'E', &a, &a, b"x.secret", MAX_RECORD + 1), Err(Refusal::Size));
    }

    #[test]
    fn check_attr_response_must_report_the_filter_for_every_path() {
        let request = b"a.secret\0d/b.secret\0";
        let good = b"a.secret\0filter\0transcrypt-v3\0d/b.secret\0filter\0transcrypt-v3\0";
        assert!(check_attr_response_ok(request, good));
        assert!(check_attr_response_ok(b"", b""));
        assert!(!check_attr_response_ok(b"", b"x"));
        assert!(!check_attr_response_ok(request, &good[..good.len() - 1]));
        let mut extra = good.to_vec();
        extra.push(b'a');
        assert!(!check_attr_response_ok(request, &extra));
        assert!(!check_attr_response_ok(request,
            b"a.secret\0filter\0unspecified\0d/b.secret\0filter\0transcrypt-v3\0"));
        assert!(!check_attr_response_ok(request,
            b"d/b.secret\0filter\0transcrypt-v3\0a.secret\0filter\0transcrypt-v3\0"));
        assert!(!check_attr_response_ok(b"a.secret\0", b"a.secret\0filter\0transcrypt-v4\0"));
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
        assert!(!parse_index_entry(&exec).unwrap().regular);
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
}
