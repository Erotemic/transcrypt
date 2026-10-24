//! Executable **legacy-v2 interoperability** with the standalone Bash tool.
//!
//! Pure byte operations are in [`core`]; Git, OpenSSL and the OS are adapters.
//! The deliberate legacy API uses MD5-era OpenSSL encryption, passes the HMAC
//! key via process argv and passes the password via child environment to
//! match v2. This is *not* a safe blueprint for the eventual authenticated
//! v3 backend. Do not use it to protect newly sensitive repositories.

#![forbid(unsafe_code)]

pub use transcrypt_legacy_core as core;

use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::process::{Command, Stdio};

use transcrypt_protocol::{encode_v2, parse_v2, V2Record};

#[cfg(unix)]
use std::os::unix::ffi::OsStringExt;

/// Error strings do not contain passwords, derived keys, or OpenSSL stderr.
#[derive(Debug)]
pub enum LegacyError {
    Command(String),
    Configuration(&'static str),
    Unsupported(&'static str),
    Io(std::io::Error),
    Format,
}

impl std::fmt::Display for LegacyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Command(msg) => write!(f, "external operation failed: {msg}"),
            Self::Configuration(msg) => write!(f, "invalid legacy configuration: {msg}"),
            Self::Unsupported(msg) => write!(f, "unsupported legacy operation: {msg}"),
            Self::Io(e) => write!(f, "I/O failed: {e}"),
            Self::Format => write!(f, "invalid legacy ciphertext envelope"),
        }
    }
}

impl std::error::Error for LegacyError {}
impl From<std::io::Error> for LegacyError {
    fn from(value: std::io::Error) -> Self { Self::Io(value) }
}

pub type Result<T> = std::result::Result<T, LegacyError>;

/// A Git-configured legacy context. Never print or derive `Debug` for secrets.
pub struct LegacySettings {
    pub cipher: String,
    pub password: Vec<u8>,
    pub openssl_path: OsString,
}

fn os_arg(bytes: Vec<u8>) -> Result<OsString> {
    if bytes.contains(&0) { return Err(LegacyError::Unsupported("NUL in argument")); }
    #[cfg(unix)]
    { Ok(OsString::from_vec(bytes)) }
    #[cfg(not(unix))]
    { String::from_utf8(bytes).map(OsString::from).map_err(|_| LegacyError::Unsupported("non-UTF8 path or password")) }
}

/// Execute a process with stdin/stdout/stderr collected separately. The
/// concurrent writer prevents a deadlock on streams larger than the OS pipe
/// capacity. No stdout is returned on child failure, even if it emitted a
/// partial plaintext prefix. Stderr is never forwarded because it may
/// accidentally contain sensitive input in diagnostics.
fn run_child(program: &OsStr, args: &[OsString], input: &[u8], env_password: Option<&[u8]>, operation: &'static str) -> Result<Vec<u8>> {
    let mut cmd = Command::new(program);
    cmd.args(args).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Some(p) = env_password {
        cmd.env("ENC_PASS", os_arg(p.to_vec())?);
    }
    let mut child = cmd.spawn()?;
    let mut input_pipe = child.stdin.take().ok_or(LegacyError::Configuration("missing stdin pipe"))?;
    std::thread::scope(|scope| {
        let writer = scope.spawn(move || -> std::io::Result<()> {
            let write = input_pipe.write_all(input);
            drop(input_pipe);
            write
        });
        let output = child.wait_with_output()?;
        let write_status = writer.join().map_err(|_| LegacyError::Command(operation.into()))?;
        if !output.status.success() {
            return Err(LegacyError::Command(operation.into()));
        }
        write_status?;
        Ok(output.stdout)
    })
}

fn argv(items: &[&str]) -> Vec<OsString> {
    items.iter().map(|s| OsString::from(*s)).collect()
}

/// Resolve a local Git config key without printing it or passing it in argv.
fn git_config(key: &str) -> Result<Option<Vec<u8>>> {
    let out = Command::new("git")
        .args(["config", "--get", "--local", key])
        .stdin(Stdio::null())
        .output()?;
    if !out.status.success() { return Ok(None); }
    let mut bytes = out.stdout;
    // Bash command substitution strips every final LF; match that behavior.
    while bytes.last() == Some(&b'\n') { bytes.pop(); }
    Ok(Some(bytes))
}

pub fn load_settings(context: &str) -> Result<LegacySettings> {
    if !core::valid_context_name(context.as_bytes()) {
        return Err(LegacyError::Configuration("invalid context name"));
    }
    let group = if context == "default" { String::new() } else { format!(".{context}") };
    let cipher = git_config(&format!("transcrypt{group}.cipher"))?
        .ok_or(LegacyError::Configuration("missing cipher"))?;
    let cipher = String::from_utf8(cipher).map_err(|_| LegacyError::Configuration("non-ASCII cipher"))?;
    // No arbitrary command-line options may come from Git config.
    if cipher.len() > 64 || cipher.is_empty() || !cipher.bytes().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'-') || !cipher.as_bytes()[0].is_ascii_alphabetic() {
        return Err(LegacyError::Configuration("invalid cipher name"));
    }
    let password = git_config(&format!("transcrypt{group}.password"))?
        .ok_or(LegacyError::Configuration("missing local credential"))?;
    let openssl_path = git_config("transcrypt.openssl-path")?
        .filter(|v| !v.is_empty())
        .map(os_arg)
        .transpose()?
        .unwrap_or_else(|| OsString::from("openssl"));
    Ok(LegacySettings { cipher, password, openssl_path })
}

/// Read exactly the HMAC digest emitted by `openssl dgst -hmac ... -sha256`.
/// OpenSSL 1.1/3 and LibreSSL may prepend different labels, so only the
/// last 64 hex digits of a successful SHA-256 invocation are significant.
fn hmac_sha256(settings: &LegacySettings, path: &[u8], plaintext: &[u8]) -> Result<[u8; 32]> {
    let key = os_arg(core::legacy_hmac_key(path, &settings.password))?;
    let args = vec![
        OsString::from("dgst"),
        OsString::from("-hmac"),
        key,
        OsString::from("-sha256"),
    ];
    let raw = run_child(&settings.openssl_path, &args, plaintext, None, "legacy HMAC")?;
    let trailing: Vec<u8> = raw.iter().copied().rev().skip_while(|c| c.is_ascii_whitespace()).take(64).collect();
    if trailing.len() != 64 { return Err(LegacyError::Format); }
    let digest_hex: Vec<u8> = trailing.into_iter().rev().collect();
    core::parse_sha256_hex(&digest_hex).ok_or(LegacyError::Format)
}

/// A v2 clean filter: deterministic ciphertext for the given filename,
/// context, and plaintext. Only the legacy v2 magic-prefix pass-through is
/// retained (its lack of verification is tracked as a v2 limitation).
pub fn clean(settings: &LegacySettings, filename: &[u8], input: &[u8]) -> Result<Vec<u8>> {
    if core::prohibited_provisional_v3(input) {
        return Err(LegacyError::Unsupported("v3 ciphertext requires a v3 filter"));
    }
    if input.is_empty() { return Ok(Vec::new()); }
    if core::legacy_looks_encrypted(input) { return Ok(input.to_vec()); }
    if filename.is_empty() { return Err(LegacyError::Configuration("empty filename")); }
    let hmac = hmac_sha256(settings, filename, input)?;
    let salt = core::legacy_salt_from_digest(&hmac);
    let salt_string = core::salt_hex(&salt);
    let args = argv(&["enc", "-e", &format!("-{}", settings.cipher), "-md", "MD5", "-S", &salt_string, "-pass", "env:ENC_PASS"]);
    let mut ciphertext = run_child(&settings.openssl_path, &args, input, Some(&settings.password), "legacy encrypt")?;
    // OpenSSL 1.1 and LibreSSL may insert the Salted__ prefix for -S,
    // whereas OpenSSL 3 does not. Reconstruct the canonical envelope once.
    if ciphertext.starts_with(b"Salted__") {
        if ciphertext.len() < 16 || ciphertext[8..16] != salt[..] {
            return Err(LegacyError::Format);
        }
        drop(ciphertext.drain(..16));
    }
    let record = V2Record { salt, ciphertext };
    encode_v2(&record).map_err(|_| LegacyError::Format)
}

/// A v2 smudge filter: non-v2 content is passed through. For a legacy v2
/// record, try OpenSSL; on wrong password or corruption the legacy contract
/// returns the original encrypted bytes. This cannot claim authentication.
pub fn smudge(settings: &LegacySettings, input: &[u8]) -> Result<Vec<u8>> {
    if core::prohibited_provisional_v3(input) {
        return Err(LegacyError::Unsupported("v3 ciphertext requires a v3 filter"));
    }
    let record = match parse_v2(input) {
        Ok(r) => r,
        Err(_) => return Ok(input.to_vec()),
    };
    let canonical = encode_v2(&record).map_err(|_| LegacyError::Format)?;
    let args = argv(&["enc", "-d", &format!("-{}", settings.cipher), "-md", "MD5", "-pass", "env:ENC_PASS", "-a"]);
    match run_child(&settings.openssl_path, &args, &canonical, Some(&settings.password), "legacy decrypt") {
        Ok(decrypted) => Ok(decrypted),
        Err(LegacyError::Command(_)) => Ok(input.to_vec()),
        Err(e) => Err(e),
    }
}

pub fn textconv(settings: &LegacySettings, input: &[u8]) -> Result<Vec<u8>> {
    smudge(settings, input)
}

/// Opaque file-path bytes are needed for exact deterministic legacy salts.
pub fn path_bytes(filename: &OsStr) -> Result<Vec<u8>> {
    #[cfg(unix)]
    { use std::os::unix::ffi::OsStrExt; Ok(filename.as_bytes().to_vec()) }
    #[cfg(not(unix))]
    { filename.to_str().map(|v| v.as_bytes().to_vec()).ok_or(LegacyError::Unsupported("non-UTF8 filename")) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn no_encryption_on_empty_or_legacy_magic() {
        let settings = LegacySettings { cipher: "aes-256-cbc".into(), password: b"public-fixture".to_vec(), openssl_path: "openssl".into() };
        assert_eq!(clean(&settings, b"name", b"").unwrap(), b"");
        assert_eq!(clean(&settings, b"name", b"U2FsdGVkAAAA").unwrap(), b"U2FsdGVkAAAA");
        assert!(clean(&settings, b"name", b"TCRYPT3:fake").is_err());
    }
}
