//! The credential agent of the private mode (`unlock --private`).
//!
//! The authenticated 64-byte key enters the child through a private pipe,
//! never through argv, the environment, an on-disk key file, or the socket.
//! Clean/smudge clients transmit their *data*, not the key. The process owns
//! the key until a successful shutdown. Unix permissions isolate other UIDs;
//! processes already running as this UID remain inside the threat boundary.
//!
//! This is the OS adapter, not part of the pure Aeneas verification target.

use std::{
    fs,
    io::{self, Read, Write},
    os::{
        fd::AsRawFd,
        unix::{fs::{DirBuilderExt, FileTypeExt, MetadataExt, PermissionsExt}, net::{UnixListener, UnixStream}},
    },
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::Duration,
};

use transcrypt_v3::{authenticate_config, clean_file, config_array, decrypt_file, SecretKey, KEY_SIZE, MAX_PATH, MAX_RECORD};
use transcrypt_v3_core::{
    authorize_agent_request, decode_be_u32, decode_frame_header, encode_be_u32, encode_frame_header, AgentOp,
    CONFIG_LEN, FRAME_HEADER_LEN,
};
use zeroize::Zeroizing;
use crate::git::sigpipe_blocked;

const SOCK: &str = "session.sock";

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum Operation {
    Ping = b'P',
    Encrypt = b'E',
    Decrypt = b'D',
    Stop = b'X',
}

fn directory(root: &Path) -> Result<PathBuf, String> {
    existing_directory(root)?.ok_or_else(|| "no local v3 session directory; run unlock".into())
}

/// `.git/transcrypt-v3`, shared by all worktrees, if it exists: the stored
/// key or the agent's socket. Anything but a real 0700 directory owned by
/// this user is refused.
pub(crate) fn existing_directory(root: &Path) -> Result<Option<PathBuf>, String> {
    let path = credential_directory(root);
    let meta = match fs::symlink_metadata(&path) {
        Ok(meta) => meta,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(_) => return Err("cannot examine .git/transcrypt-v3".into()),
    };
    if !meta.is_dir() || meta.file_type().is_symlink() || meta.permissions().mode() & 0o077 != 0 || meta.uid() != euid() {
        return Err("unsafe local v3 credential directory; require a real 0700 directory owned by this user".into());
    }
    Ok(Some(path))
}

fn euid() -> u32 {
    // SAFETY: geteuid has no preconditions and cannot fail.
    unsafe { libc::geteuid() as u32 }
}

/// The effective UID of the process at the other end of a Unix socket, as
/// recorded by the kernel when the connection was made.
fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    {
        // SAFETY: `cred` and `len` describe a writable ucred buffer.
        let mut cred: libc::ucred = unsafe { std::mem::zeroed() };
        let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        let rc = unsafe {
            libc::getsockopt(stream.as_raw_fd(), libc::SOL_SOCKET, libc::SO_PEERCRED,
                (&mut cred as *mut libc::ucred).cast(), &mut len)
        };
        if rc != 0 { return Err(io::Error::last_os_error()); }
        Ok(cred.uid as u32)
    }
    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    {
        let (mut uid, mut gid) = (0, 0);
        // SAFETY: both out-pointers are valid.
        if unsafe { libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(uid as u32)
    }
}

/// Both ends refuse a peer running as another user. The 0700 directory
/// already denies other users; this also holds if the socket inode is ever
/// reachable another way. Same-UID peers remain inside the trust boundary.
fn same_user(stream: &UnixStream) -> Result<(), String> {
    match peer_uid(stream) {
        Ok(uid) if uid == euid() => Ok(()),
        _ => Err("v3 credential socket peer is not this user".into()),
    }
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
            fs::DirBuilder::new().mode(0o700).create(&path)
                .map_err(|e| format!("cannot create the credential directory: {e}"))?;
        },
        Err(e) => return Err(format!("cannot examine the credential directory: {e}")),
    }
    directory(root)
}

/// Unix socket addresses are limited to ~104 (macOS) or 108 (Linux) bytes,
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
fn connect(dir: &Path) -> Result<io::Result<UnixStream>, String> {
    at_socket(dir, |p| UnixStream::connect(p))
}

fn check_socket(path: &Path) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|_| "v3 session is locked; run unlock")?;
    if !meta.file_type().is_socket() || meta.permissions().mode() & 0o077 != 0 || meta.uid() != euid() {
        return Err("unsafe v3 session socket; expected mode 0600 and owned by this user".into());
    }
    Ok(())
}

fn reply(stream: &mut UnixStream, response: Result<Vec<u8>, String>) -> io::Result<()> {
    let (status, data) = match response {
        Ok(value) => (0u8, value),
        Err(message) => (1u8, message.into_bytes()),
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
pub(crate) fn request(root: &Path, config: &[u8], op: Operation, path_bytes: &[u8], body: &[u8]) -> Result<Zeroizing<Vec<u8>>, String> {
    let config: &[u8; CONFIG_LEN] = config.try_into().map_err(|_| "invalid v3 agent request length")?;
    if body.len() > MAX_RECORD || path_bytes.len() > MAX_PATH {
        return Err("invalid v3 agent request length".into());
    }
    let dir = directory(root)?;
    check_socket(&dir.join(SOCK))?;
    let mut stream = connect(&dir)?.map_err(|_| "v3 credential agent is not running; run unlock")?;
    // Plaintext is about to be sent to, or accepted from, this peer.
    same_user(&stream)?;
    // Bound a broken local peer rather than hanging a Git operation forever.
    stream.set_read_timeout(Some(Duration::from_secs(120)))
        .map_err(|_| "cannot set agent read timeout")?;
    stream.set_write_timeout(Some(Duration::from_secs(120)))
        .map_err(|_| "cannot set agent write timeout")?;
    // Frame layout is defined (and proved to roundtrip) by the verified core.
    sigpipe_blocked(|| {
        stream.write_all(&encode_frame_header(op as u8, config, path_bytes.len() as u32))?;
        stream.write_all(path_bytes)?;
        stream.write_all(&encode_be_u32(body.len() as u32))?;
        stream.write_all(body)
    }).map_err(|_| "cannot send the request to the credential agent")?;
    let mut header = [0u8; 5];
    stream.read_exact(&mut header).map_err(|_| "credential agent failed before replying")?;
    let size = decode_be_u32(header[1..5].try_into().map_err(|_| "malformed agent response")?) as usize;
    if size > MAX_RECORD { return Err("credential agent response exceeds limit".into()); }
    let mut value = Zeroizing::new(vec![0u8; size]);
    stream.read_exact(&mut value).map_err(|_| "incomplete credential agent response")?;
    match header[0] {
        0 => Ok(value),
        1 => Err(format!("credential agent: {}", String::from_utf8_lossy(&value))),
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
    match fs::symlink_metadata(&path) {
        Ok(meta) => {
            if !meta.file_type().is_socket() { return Err("unsafe existing session socket path".into()); }
            if connect(&dir)?.is_ok() {
                // An agent whose worktree config has changed (a pulled rekey)
                // stops when it refuses this request; give it a moment.
                let _ = request(root, config, Operation::Ping, &[], &[]);
                let stale = (0..40).any(|_| {
                    thread::sleep(Duration::from_millis(25));
                    fs::symlink_metadata(&path).is_err()
                        || connect(&dir).is_ok_and(|r| r.is_err())
                });
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
        Err(e) if e.kind() == io::ErrorKind::NotFound => {},
        Err(_) => return Err("cannot examine session socket".into()),
    }
    start_agent(root, config, key, idle)
}

fn start_agent(root: &Path, config: &[u8], key: &SecretKey, idle: Option<Duration>) -> Result<(), String> {
    let executable = std::env::current_exe().map_err(|_| "cannot locate executable for credential agent")?;
    let mut child = Command::new(executable)
        .arg("serve")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn().map_err(|e| format!("cannot spawn credential agent: {e}"))?;
    // The key, then the idle limit in seconds (0: none), over the pipe.
    let idle_seconds = idle.map_or(0u64, |d| d.as_secs().max(1));
    let sent = child.stdin.take().ok_or("agent key pipe missing")
        .map(|mut pipe| sigpipe_blocked(|| pipe.write_all(&key[..]).and_then(|_| pipe.write_all(&idle_seconds.to_be_bytes()))))?;
    if sent.is_err() {
        let _ = child.kill();
        let _ = child.wait();
        return Err("cannot deliver key through private pipe".into());
    }
    let mut last = "agent is not ready".to_owned();
    for _ in 0..120 {
        match request(root, config, Operation::Ping, &[], &[]) {
            Ok(_) => return Ok(()),
            Err(e) => last = e,
        }
        match child.try_wait() {
            Ok(Some(_)) => return Err("credential agent exited during startup".into()),
            Err(_) => return Err("cannot inspect credential agent process".into()),
            Ok(None) => {},
        }
        thread::sleep(Duration::from_millis(25));
    }
    let _ = child.kill();
    let _ = child.wait();
    Err(format!("credential agent startup timed out: {last}"))
}

pub(crate) fn stop(root: &Path, config: &[u8]) -> Result<(), String> {
    request(root, config, Operation::Stop, &[], &[])?;
    // The server unlinks its own socket on exit. The agent key is erased when
    // the process exits; we do not claim erasure of OS swap or crash dumps.
    for _ in 0..40 {
        if fs::symlink_metadata(directory(root)?.join(SOCK)).is_err() { return Ok(()); }
        thread::sleep(Duration::from_millis(25));
    }
    Err("agent acknowledged shutdown but socket still exists".into())
}

fn transaction(stream: &mut UnixStream, config: &[u8; CONFIG_LEN], key: &SecretKey) -> Result<bool, String> {
    let mut raw = [0u8; FRAME_HEADER_LEN];
    stream.read_exact(&mut raw).map_err(|_| "incomplete agent request header")?;
    let header = decode_frame_header(&raw);
    let path_len = header.path_len as usize;
    if path_len > MAX_PATH { return Err("oversized agent Git pathname".into()); }
    let mut path_bytes = vec![0u8; path_len];
    stream.read_exact(&mut path_bytes).map_err(|_| "incomplete agent pathname")?;
    let mut size_bytes = [0u8; 4];
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

/// Process hardening for every v3 process (all of them handle keys or
/// plaintext): no core dumps and, on Linux, not dumpable, which also stops
/// same-UID processes from attaching with ptrace or reading /proc/PID/mem.
/// It does not protect against root or against use of the agent socket.
pub(crate) fn harden_process() -> Result<(), String> {
    let none = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    // SAFETY: setrlimit reads a valid, fully initialized rlimit struct.
    if unsafe { libc::setrlimit(libc::RLIMIT_CORE, &none) } != 0 {
        return Err("cannot disable core dumps".into());
    }
    #[cfg(target_os = "linux")]
    // SAFETY: PR_SET_DUMPABLE takes integer arguments only.
    if unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0) } != 0 {
        return Err("cannot mark process non-dumpable".into());
    }
    Ok(())
}

/// Close every descriptor inherited beyond stdio, so the long-lived agent
/// never keeps a caller's pipes, files or locks open.
fn close_inherited_fds() {
    let fds: Vec<i32> = fs::read_dir("/dev/fd")
        .map(|dir| dir.filter_map(|e| e.ok()?.file_name().to_str()?.parse().ok()).collect())
        .unwrap_or_default();
    for fd in fds.into_iter().filter(|fd| *fd > 2) {
        // SAFETY: nothing in this process uses these descriptors yet; closing
        // an already closed one (the directory listing's own) is harmless.
        unsafe { libc::close(fd) };
    }
}

/// Internal child entrypoint. Runs until explicit lock or a process shutdown.
pub(crate) fn serve(root: &Path, config: &[u8]) -> Result<(), String> {
    close_inherited_fds();
    let config = config_array(config)?;
    let mut key: SecretKey = Zeroizing::new([0u8; KEY_SIZE]);
    // Keep the key page out of swap where the OS allows it (best effort:
    // RLIMIT_MEMLOCK may forbid it; the key is still never written to disk).
    // SAFETY: the pointer and length describe `key`, which outlives the lock.
    let _ = unsafe { libc::mlock(key.as_ptr().cast(), KEY_SIZE) };
    io::stdin().read_exact(&mut key[..]).map_err(|_| "missing private startup key")?;
    let mut idle = [0u8; 8];
    io::stdin().read_exact(&mut idle).map_err(|_| "missing agent idle limit")?;
    let idle_ms: i32 = match u64::from_be_bytes(idle) {
        0 => -1,
        seconds => i32::try_from(seconds.saturating_mul(1000)).unwrap_or(i32::MAX),
    };
    authenticate_config(config, &key)?;
    let dir = directory(root)?;
    let path = dir.join(SOCK);
    let listener = at_socket(&dir, |p| UnixListener::bind(p))?.map_err(|e| format!("cannot bind private credential socket: {e}"))?;
    fs::set_permissions(&path, fs::Permissions::from_mode(0o600))
        .map_err(|_| "cannot secure session socket")?;
    loop {
        // Wait for a client; past the idle limit, forget the key.
        let mut ready = libc::pollfd { fd: listener.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one valid pollfd for the listener's open descriptor.
        match unsafe { libc::poll(&mut ready, 1, idle_ms) } {
            0 => break,
            n if n < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted => continue,
            n if n < 0 => break,
            _ => {},
        }
        let mut stream = match listener.accept() { Ok((s, _)) => s, Err(_) => break };
        // A stalled client must not hold the single-threaded agent forever.
        stream.set_read_timeout(Some(Duration::from_secs(120)))
            .map_err(|_| "cannot set agent inbound timeout")?;
        stream.set_write_timeout(Some(Duration::from_secs(120)))
            .map_err(|_| "cannot set agent outbound timeout")?;
        if same_user(&stream).is_err() { continue; }
        match transaction(&mut stream, config, &key) {
            Ok(true) => break,
            Ok(false) => {},
            Err(message) => {
                let _ = reply(&mut stream, Err(message));
                // A refused request may come from a checkout whose config has
                // since changed (a pulled rekey). If this agent's own
                // worktree no longer has its config, its key is obsolete.
                if fs::read(root.join(".transcrypt/config")).ok().as_deref() != Some(&config[..]) {
                    break;
                }
            },
        }
    }
    drop(listener);
    let _ = fs::remove_file(&path);
    Ok(())
}
