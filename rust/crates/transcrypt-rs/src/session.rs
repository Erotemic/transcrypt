//! The credential agent of the private mode (`unlock --private`).
//!
//! The authenticated 64-byte key enters the child through a private pipe,
//! never through argv, the environment, an on-disk key file, or the socket.
//! Clean/smudge clients transmit their *data*, not the key. The process owns
//! the key until a successful shutdown. Unix permissions (on Windows, an
//! owner-only DACL) isolate other users; processes already running as this
//! user remain inside the threat boundary. The socket is a Unix-domain
//! socket on both (Windows 10 1803 and later have them); `os` supplies it.
//!
//! This is the OS adapter, not part of the pure Aeneas verification target.

use crate::modes::Privacy;
use std::{
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::Duration,
};

use transcrypt_rs::{authenticate_config, clean_file, config_array, decrypt_file, SecretKey, KEY_SIZE, MAX_PATH, MAX_RECORD};
use transcrypt_v3_core::{
    authorize_agent_request, decode_be_u32, decode_frame_header, encode_be_u32, encode_frame_header, AgentOp,
    BE_U32_LEN, CONFIG_LEN, FRAME_HEADER_LEN,
};
use zeroize::Zeroizing;
use crate::os::{self, sigpipe_blocked, Listener, Stream};

const SOCK: &str = "session.sock";
/// The first byte of a reply: the rest is the result, or the refusal.
const REPLY_OK: u8 = 0;
const REPLY_ERR: u8 = 1;
/// How long the client waits between checks of the agent's socket.
const POLL: Duration = Duration::from_millis(25);
/// How long `poll` waits for a change of the agent's socket.
const SETTLE_WAIT: Duration = Duration::from_secs(1);
/// How long a new agent has to answer its first request.
const STARTUP_WAIT: Duration = Duration::from_secs(3);
/// The longest either end waits on a stalled peer.
const SOCKET_TIMEOUT: Duration = Duration::from_secs(120);
/// The number of `POLL` pauses in `wait`.
const fn polls(wait: Duration) -> u128 { wait.as_millis() / POLL.as_millis() }
/// A reply's header: its status byte, then the length of its result.
const STATUS_LEN: usize = 1;
const REPLY_HEADER_LEN: usize = STATUS_LEN + BE_U32_LEN;
/// The idle limit the agent receives (in seconds, big-endian) for none.
const NO_IDLE_LIMIT: u64 = 0;
/// The shortest idle limit sent: a sub-second limit is not "none".
const MIN_IDLE_SECONDS: u64 = 1;
// Every request length fits the frame's 32-bit fields (`request` checks
// them against these bounds before sending).
const _: () = assert!(MAX_RECORD <= u32::MAX as usize);
const _: () = assert!(MAX_PATH <= u32::MAX as usize);

/// The opcode byte of `op` on the wire: the one the verified
/// `authorize_agent_request` maps back to `op` (tested below).
fn opcode(op: AgentOp) -> u8 {
    match op {
        AgentOp::Ping => b'P',
        AgentOp::Encrypt => b'E',
        AgentOp::Decrypt => b'D',
        AgentOp::Stop => b'X',
    }
}

/// Whether `done` holds within about `SETTLE_WAIT`, checked after each pause.
fn poll(mut done: impl FnMut() -> Result<bool, String>) -> Result<bool, String> {
    for _ in 0..polls(SETTLE_WAIT) {
        thread::sleep(POLL);
        if done()? { return Ok(true); }
    }
    Ok(false)
}

fn directory(root: &Path) -> Result<PathBuf, String> {
    existing_directory(root)?.ok_or_else(|| "no local v3 session directory; run unlock".into())
}

/// `.git/transcrypt-v3`, shared by all worktrees, if it exists: the stored
/// key or the agent's socket. Anything but a real directory that only this
/// user, who owns it, can enter is refused.
pub(crate) fn existing_directory(root: &Path) -> Result<Option<PathBuf>, String> {
    let path = credential_directory(root);
    match os::private_directory(&path) {
        Ok(Privacy::Missing) => Ok(None),
        Ok(Privacy::Private) => Ok(Some(path)),
        Ok(Privacy::Exposed(why)) => Err(format!("unsafe local v3 credential directory .git/transcrypt-v3: {why}; \
            require a real {:04o} directory owned by this user", crate::modes::PRIVATE_DIR)),
        Err(_) => Err("cannot examine .git/transcrypt-v3".into()),
    }
}

/// Both ends refuse a peer running as another user. The private directory
/// already denies other users; this also holds if the socket is ever
/// reachable another way. Same-user peers remain inside the trust boundary.
fn same_user(stream: &Stream) -> Result<(), String> {
    if os::peer_is_this_user(stream) { Ok(()) } else { Err("v3 credential socket peer is not this user".into()) }
}

/// `.git/transcrypt-v3`, whether or not it exists.
fn credential_directory(root: &Path) -> PathBuf {
    crate::git::common_dir(root).join("transcrypt-v3")
}

pub(crate) fn prepare_directory(root: &Path) -> Result<PathBuf, String> {
    let path = credential_directory(root);
    match fs::symlink_metadata(&path) {
        Ok(_) => {},
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            os::create_private_directory(&path)
                .map_err(|e| format!("cannot create the credential directory: {e}"))?;
        },
        Err(e) => return Err(format!("cannot examine the credential directory: {e}")),
    }
    directory(root)
}

/// Socket addresses are limited to ~104 (macOS) or 108 (Linux, Windows) bytes,
/// which a deep repository path easily exceeds. The socket is bound and
/// connected by its bare name from inside its (checked) directory; v3
/// processes are single-threaded while they do so. Ownership and permission
/// checks still use the absolute path.
fn at_socket<T>(dir: &Path, f: impl FnOnce(&Path) -> io::Result<T>) -> Result<io::Result<T>, String> {
    let previous = std::env::current_dir().map_err(|_| "cannot read working directory")?;
    std::env::set_current_dir(dir).map_err(|_| "cannot enter the session directory")?;
    let result = f(Path::new(SOCK));
    std::env::set_current_dir(&previous).map_err(|_| "cannot return to the repository root")?;
    Ok(result)
}

/// Connect to the agent's socket in `dir`.
fn connect(dir: &Path) -> Result<io::Result<Stream>, String> {
    at_socket(dir, |p| Stream::connect(p))
}

fn check_socket(path: &Path) -> Result<(), String> {
    match os::is_socket(path) {
        Ok(Some(_)) if os::private_socket(path) => Ok(()),
        Ok(Some(_)) => Err(format!("unsafe v3 session socket; expected mode {:04o} and owned by this user",
            crate::modes::PRIVATE_FILE)),
        _ => Err("v3 session is locked; run unlock".into()),
    }
}

/// Bound a stalled or broken peer (either end) instead of hanging forever.
fn set_timeouts(stream: &Stream) -> Result<(), String> {
    os::set_timeouts(stream, SOCKET_TIMEOUT).map_err(|_| "cannot set the credential socket timeouts".into())
}

fn reply(stream: &mut Stream, response: Result<Vec<u8>, String>) -> io::Result<()> {
    let (status, data) = match response {
        Ok(value) => (REPLY_OK, value),
        Err(message) => (REPLY_ERR, message.into_bytes()),
    };
    let data = Zeroizing::new(data);
    let length = u32::try_from(data.len()).map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "oversized response"))?;
    stream.write_all(&[status])?;
    stream.write_all(&encode_be_u32(length))?;
    stream.write_all(&data)?;
    stream.flush()
}

/// A single operation on the *live* agent. The caller sends the complete
/// public config each time: a stale agent cannot authorize a newly changed
/// configuration merely because the directory or socket still exists.
pub(crate) fn request(root: &Path, config: &[u8], op: AgentOp, path_bytes: &[u8], body: &[u8]) -> Result<Zeroizing<Vec<u8>>, String> {
    let config: &[u8; CONFIG_LEN] = config.try_into().map_err(|_| "invalid v3 agent request length")?;
    if body.len() > MAX_RECORD || path_bytes.len() > MAX_PATH {
        return Err("invalid v3 agent request length".into());
    }
    let dir = directory(root)?;
    check_socket(&dir.join(SOCK))?;
    let mut stream = connect(&dir)?.map_err(|_| "v3 credential agent is not running; run unlock")?;
    // Plaintext is about to be sent to, or accepted from, this peer.
    same_user(&stream)?;
    set_timeouts(&stream)?;
    // Frame layout is defined (and proved to roundtrip) by the verified core.
    // The `as u32` casts are exact: both lengths were bounded above.
    sigpipe_blocked(&mut stream, |stream| {
        stream.write_all(&encode_frame_header(opcode(op), config, path_bytes.len() as u32))?;
        stream.write_all(path_bytes)?;
        stream.write_all(&encode_be_u32(body.len() as u32))?;
        stream.write_all(body)
    }).map_err(|_| "cannot send the request to the credential agent")?;
    // The status byte, then the result's length.
    let mut header = [0u8; REPLY_HEADER_LEN];
    stream.read_exact(&mut header).map_err(|_| "credential agent failed before replying")?;
    let size = decode_be_u32(header[STATUS_LEN..].try_into().map_err(|_| "malformed agent response")?) as usize;
    if size > MAX_RECORD { return Err("credential agent response exceeds limit".into()); }
    let mut value = Zeroizing::new(vec![0u8; size]);
    stream.read_exact(&mut value).map_err(|_| "incomplete credential agent response")?;
    match header[0] {
        REPLY_OK => Ok(value),
        REPLY_ERR => Err(format!("credential agent: {}", String::from_utf8_lossy(&value))),
        _ => Err("malformed agent response status".into()),
    }
}

/// Derive and authenticate *before* this function is called. The process key
/// arrives by pipe, and the parent does not persist it anywhere on disk. With
/// `idle`, the agent forgets the key and exits after that long without a
/// request (session expiration).
pub(crate) fn start(root: &Path, config: &[u8], key: &SecretKey, idle: Option<Duration>) -> Result<(), String> {
    let dir = prepare_directory(root)?;
    let path = dir.join(SOCK);
    match os::is_socket(&path) {
        Ok(Some(socket)) => {
            if !socket { return Err("unsafe existing session socket path".into()); }
            if connect(&dir)?.is_ok() {
                // An agent whose worktree config has changed (a pulled rekey)
                // stops when it refuses this request; give it a moment.
                let _ = request(root, config, AgentOp::Ping, &[], &[]);
                let stale = poll(|| Ok(fs::symlink_metadata(&path).is_err()
                    || connect(&dir).is_ok_and(|r| r.is_err())))?;
                if !stale {
                    return Err("an agent for another .transcrypt/config is running (another worktree?); \
                        lock it there first".into());
                }
            }
            // A dead process may leave its socket inode (unless the stale
            // agent removed it); our 0700 parent is owned by this checkout's
            // user. Refuse non-socket substitutes.
            if fs::symlink_metadata(&path).is_ok() {
                fs::remove_file(&path).map_err(|_| "cannot remove stale agent socket")?;
            }
        },
        Ok(None) => {},
        Err(_) => return Err("cannot examine session socket".into()),
    }
    start_agent(root, config, key, idle)
}

fn start_agent(root: &Path, config: &[u8], key: &SecretKey, idle: Option<Duration>) -> Result<(), String> {
    let executable = std::env::current_exe().map_err(|_| "cannot locate executable for credential agent")?;
    let mut command = Command::new(executable);
    command.arg("serve").current_dir(root).stdin(Stdio::piped()).stdout(Stdio::null()).stderr(Stdio::null());
    os::detach(&mut command);
    let mut child = command.spawn().map_err(|e| format!("cannot spawn credential agent: {e}"))?;
    // The key, then the idle limit in seconds (0: none), over the pipe.
    let idle_seconds = idle.map_or(NO_IDLE_LIMIT, |d| d.as_secs().max(MIN_IDLE_SECONDS));
    let sent = child.stdin.take().ok_or("agent key pipe missing")
        .map(|mut pipe| sigpipe_blocked(&mut pipe, |pipe| pipe.write_all(&key[..]).and_then(|_| pipe.write_all(&idle_seconds.to_be_bytes()))))?;
    if sent.is_err() {
        let _ = child.kill();
        let _ = child.wait();
        return Err("cannot deliver key through private pipe".into());
    }
    let mut last = "agent is not ready".to_owned();
    for _ in 0..polls(STARTUP_WAIT) {
        match request(root, config, AgentOp::Ping, &[], &[]) {
            Ok(_) => return Ok(()),
            Err(e) => last = e,
        }
        match child.try_wait() {
            Ok(Some(_)) => return Err("credential agent exited during startup".into()),
            Err(_) => return Err("cannot inspect credential agent process".into()),
            Ok(None) => {},
        }
        thread::sleep(POLL);
    }
    let _ = child.kill();
    let _ = child.wait();
    Err(format!("credential agent startup timed out: {last}"))
}

pub(crate) fn stop(root: &Path, config: &[u8]) -> Result<(), String> {
    request(root, config, AgentOp::Stop, &[], &[])?;
    // The server unlinks its own socket on exit. The agent key is erased when
    // the process exits; we do not claim erasure of OS swap or crash dumps.
    if poll(|| Ok(fs::symlink_metadata(directory(root)?.join(SOCK)).is_err()))? { return Ok(()); }
    Err("agent acknowledged shutdown but socket still exists".into())
}

fn transaction(stream: &mut Stream, config: &[u8; CONFIG_LEN], key: &SecretKey) -> Result<bool, String> {
    let mut raw = [0u8; FRAME_HEADER_LEN];
    stream.read_exact(&mut raw).map_err(|_| "incomplete agent request header")?;
    let header = decode_frame_header(&raw);
    let path_len = header.path_len as usize;
    if path_len > MAX_PATH { return Err("oversized agent Git pathname".into()); }
    let mut path_bytes = vec![0u8; path_len];
    stream.read_exact(&mut path_bytes).map_err(|_| "incomplete agent pathname")?;
    let mut size_bytes = [0u8; BE_U32_LEN];
    stream.read_exact(&mut size_bytes).map_err(|_| "incomplete agent length")?;
    let size = decode_be_u32(&size_bytes) as usize;
    // The verified core decides, before the body is read, whether this
    // request is permitted under the configuration authenticated at startup.
    let action = authorize_agent_request(header.opcode, &header.config, config, &path_bytes, size)
        .map_err(|_| "agent request refused: config, path, size or opcode not permitted")?;
    let mut body = Zeroizing::new(vec![0u8; size]);
    stream.read_exact(&mut body).map_err(|_| "incomplete agent body")?;
    let result = match action {
        AgentOp::Ping => Ok(Vec::new()),
        AgentOp::Encrypt => clean_file(config, key, &path_bytes, &body),
        AgentOp::Decrypt => decrypt_file(config, key, &path_bytes, &body)
            .map(|mut plaintext| std::mem::take(&mut *plaintext)),
        AgentOp::Stop => {
            reply(stream, Ok(Vec::new())).map_err(|_| "cannot acknowledge agent shutdown")?;
            return Ok(true);
        },
    };
    reply(stream, result).map_err(|_| "cannot send agent response")?;
    Ok(false)
}

/// Internal child entrypoint. Runs until explicit lock or a process shutdown.
pub(crate) fn serve(root: &Path, config: &[u8]) -> Result<(), String> {
    os::close_inherited();
    let config = config_array(config)?;
    let mut key: SecretKey = Zeroizing::new([0u8; KEY_SIZE]);
    // Keep the key page out of swap where the OS allows it (best effort;
    // the key is still never written to disk).
    os::lock_memory(key.as_ptr(), KEY_SIZE);
    io::stdin().read_exact(&mut key[..]).map_err(|_| "missing private startup key")?;
    let mut idle = [0u8; size_of::<u64>()];
    io::stdin().read_exact(&mut idle).map_err(|_| "missing agent idle limit")?;
    let idle = match u64::from_be_bytes(idle) {
        NO_IDLE_LIMIT => None,
        seconds => Some(Duration::from_secs(seconds)),
    };
    authenticate_config(config, &key)?;
    let dir = directory(root)?;
    let path = dir.join(SOCK);
    let listener = at_socket(&dir, |p| Listener::bind(p))?.map_err(|e| format!("cannot bind private credential socket: {e}"))?;
    os::secure_socket(&path).map_err(|_| "cannot secure session socket")?;
    // Wait for each client; past the idle limit, forget the key.
    while let Some(mut stream) = os::accept(&listener, idle) {
        // A stalled client must not hold the single-threaded agent forever.
        // One already gone can refuse the timeouts (macOS: EINVAL once the
        // peer has closed); it is dropped, and the agent keeps serving.
        if set_timeouts(&stream).is_err() || same_user(&stream).is_err() { continue; }
        match transaction(&mut stream, config, &key) {
            Ok(true) => break,
            Ok(false) => {},
            Err(message) => {
                let _ = reply(&mut stream, Err(message));
                // A refused request may come from a checkout whose config has
                // since changed (a pulled rekey). If this agent's own
                // worktree no longer has its config, its key is obsolete.
                if fs::read(root.join(crate::git::CONFIG_PATH)).ok().as_deref() != Some(&config[..]) {
                    break;
                }
            },
        }
    }
    drop(listener);
    let _ = fs::remove_file(&path);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each opcode the client sends is the one the agent's verified check
    /// authorizes as that operation.
    #[test]
    fn opcodes_authorize_as_their_operation() {
        let config = [0u8; CONFIG_LEN];
        for op in [AgentOp::Ping, AgentOp::Encrypt, AgentOp::Decrypt, AgentOp::Stop] {
            let path: &[u8] = if matches!(op, AgentOp::Encrypt | AgentOp::Decrypt) { b"x.env" } else { b"" };
            assert_eq!(authorize_agent_request(opcode(op), &config, &config, path, 0), Ok(op));
        }
    }
}
