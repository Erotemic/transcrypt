//! Unix credential agent for the v3 proof of concept.
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
    os::unix::{fs::{DirBuilderExt, FileTypeExt, PermissionsExt}, net::{UnixListener, UnixStream}},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::Duration,
};

use transcrypt_v3::{authenticate_config, decrypt_file, encrypt_file, validate_protected_path, SecretKey, KEY_SIZE, MAX_FILE, MAX_PATH};
use transcrypt_v3_core::{CONFIG_LEN, FILE_MIN_LEN};
use zeroize::Zeroizing;

const SOCK: &str = "session.sock";
const WIRE_LIMIT: usize = MAX_FILE + FILE_MIN_LEN;
const MAX_RESPONSE: usize = WIRE_LIMIT;

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum Operation {
    Ping = b'P',
    Encrypt = b'E',
    Decrypt = b'D',
    Stop = b'X',
}

fn directory(root: &Path) -> Result<PathBuf, String> {
    let path = root.join(".git/transcrypt-v3");
    let meta = fs::symlink_metadata(&path).map_err(|_| "no local v3 session directory; run unlock")?;
    if !meta.is_dir() || meta.file_type().is_symlink() || meta.permissions().mode() & 0o077 != 0 {
        return Err("unsafe local v3 session directory; require a real 0700 directory".into());
    }
    Ok(path)
}

fn prepare_directory(root: &Path) -> Result<PathBuf, String> {
    let path = root.join(".git/transcrypt-v3");
    match fs::symlink_metadata(&path) {
        Ok(_) => {},
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            fs::DirBuilder::new().mode(0o700).create(&path)
                .map_err(|e| format!("cannot create session directory: {e}"))?;
        },
        Err(e) => return Err(format!("cannot examine session directory: {e}")),
    }
    let path = directory(root)?;
    // Never silently leave the previous proof-of-concept's disk key behind.
    // Users can `lock` with the earlier binary before applying this update.
    if fs::symlink_metadata(path.join("key")).is_ok() {
        return Err("old v3 on-disk key found; lock with the prior binary or remove .git/transcrypt-v3/key before unlocking".into());
    }
    Ok(path)
}

fn socket(root: &Path) -> Result<PathBuf, String> {
    Ok(directory(root)?.join(SOCK))
}

fn check_socket(path: &Path) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|_| "v3 session is locked; run unlock")?;
    if !meta.file_type().is_socket() || meta.permissions().mode() & 0o077 != 0 {
        return Err("unsafe v3 session socket; expected mode 0600".into());
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
    stream.write_all(&length.to_be_bytes())?;
    stream.write_all(&data)?;
    stream.flush()
}

/// A single operation on the *live* agent. The caller sends the complete
/// public config each time: a stale agent cannot authorize a newly changed
/// configuration merely because the directory or socket still exists.
pub(crate) fn request(root: &Path, config: &[u8], op: Operation, path_bytes: &[u8], body: &[u8]) -> Result<Vec<u8>, String> {
    if config.len() != CONFIG_LEN || body.len() > WIRE_LIMIT || path_bytes.len() > MAX_PATH {
        return Err("invalid v3 agent request length".into());
    }
    let path = socket(root)?;
    check_socket(&path)?;
    let mut stream = UnixStream::connect(&path).map_err(|_| "v3 credential agent is not running; run unlock")?;
    // Bound a broken local peer rather than hanging a Git operation forever.
    stream.set_read_timeout(Some(Duration::from_secs(120)))
        .map_err(|_| "cannot set agent read timeout")?;
    stream.set_write_timeout(Some(Duration::from_secs(120)))
        .map_err(|_| "cannot set agent write timeout")?;
    stream.write_all(&[op as u8]).map_err(|_| "cannot send agent operation")?;
    stream.write_all(config).map_err(|_| "cannot send public config")?;
    stream.write_all(&(path_bytes.len() as u32).to_be_bytes()).map_err(|_| "cannot send path length")?;
    stream.write_all(path_bytes).map_err(|_| "cannot send protected Git pathname")?;
    stream.write_all(&(body.len() as u32).to_be_bytes()).map_err(|_| "cannot send body length")?;
    stream.write_all(body).map_err(|_| "cannot send agent input")?;
    let mut header = [0u8; 5];
    stream.read_exact(&mut header).map_err(|_| "credential agent failed before replying")?;
    let size = u32::from_be_bytes(header[1..5].try_into().map_err(|_| "malformed agent response")?) as usize;
    if size > MAX_RESPONSE { return Err("credential agent response exceeds limit".into()); }
    let mut value = vec![0u8; size];
    stream.read_exact(&mut value).map_err(|_| "incomplete credential agent response")?;
    match header[0] {
        0 => Ok(value),
        1 => Err(format!("credential agent: {}", String::from_utf8_lossy(&value))),
        _ => Err("malformed agent response status".into()),
    }
}

/// Derive and authenticate *before* this function is called. The process key
/// arrives by pipe, and the parent does not persist it anywhere on disk.
pub(crate) fn start(root: &Path, config: &[u8], key: &SecretKey) -> Result<(), String> {
    let path = prepare_directory(root)?.join(SOCK);
    match fs::symlink_metadata(&path) {
        Ok(meta) => {
            if !meta.file_type().is_socket() { return Err("unsafe existing session socket path".into()); }
            if UnixStream::connect(&path).is_ok() {
                return Err("already unlocked: an agent is running".into());
            }
            // A dead process may leave its socket inode; our 0700 parent is
            // owned by this checkout's user. Refuse non-socket substitutes.
            fs::remove_file(&path).map_err(|_| "cannot remove stale agent socket")?;
        },
        Err(e) if e.kind() == io::ErrorKind::NotFound => {},
        Err(_) => return Err("cannot examine session socket".into()),
    }
    let executable = std::env::current_exe().map_err(|_| "cannot locate executable for credential agent")?;
    let mut child = Command::new(executable)
        .arg("serve")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn().map_err(|e| format!("cannot spawn credential agent: {e}"))?;
    let sent = child.stdin.take().ok_or("agent key pipe missing")?
        .write_all(&key[..]);
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
        if fs::symlink_metadata(socket(root)?).is_err() { return Ok(()); }
        thread::sleep(Duration::from_millis(25));
    }
    Err("agent acknowledged shutdown but socket still exists".into())
}

fn transaction(stream: &mut UnixStream, config: &[u8], key: &SecretKey) -> Result<bool, String> {
    let mut op = [0u8; 1];
    stream.read_exact(&mut op).map_err(|_| "incomplete agent operation")?;
    let mut supplied_config = [0u8; CONFIG_LEN];
    stream.read_exact(&mut supplied_config).map_err(|_| "incomplete agent config")?;
    let mut path_len_bytes = [0u8; 4];
    stream.read_exact(&mut path_len_bytes).map_err(|_| "incomplete agent path length")?;
    let path_len = u32::from_be_bytes(path_len_bytes) as usize;
    if path_len > MAX_PATH { return Err("oversized agent Git pathname".into()); }
    let mut path_bytes = vec![0u8; path_len];
    stream.read_exact(&mut path_bytes).map_err(|_| "incomplete agent pathname")?;
    let mut size_bytes = [0u8; 4];
    stream.read_exact(&mut size_bytes).map_err(|_| "incomplete agent length")?;
    let size = u32::from_be_bytes(size_bytes) as usize;
    if size > WIRE_LIMIT { return Err("oversized agent payload".into()); }
    if supplied_config != config { return Err("active agent's public config differs from checkout".into()); }
    let mut body = Zeroizing::new(vec![0u8; size]);
    stream.read_exact(&mut body).map_err(|_| "incomplete agent body")?;
    let result = match op[0] {
        b'P' if size == 0 && path_bytes.is_empty() => Ok(Vec::new()),
        b'E' => {
            validate_protected_path(&path_bytes)?;
            encrypt_file(config, key, &path_bytes, &body)
        },
        b'D' => {
            validate_protected_path(&path_bytes)?;
            decrypt_file(config, key, &path_bytes, &body)
        },
        b'X' if size == 0 && path_bytes.is_empty() => {
            reply(stream, Ok(Vec::new())).map_err(|_| "cannot acknowledge agent shutdown")?;
            return Ok(true);
        },
        _ => Err("unsupported agent operation".into()),
    };
    reply(stream, result).map_err(|_| "cannot send agent response")?;
    Ok(false)
}

/// Internal child entrypoint. Runs until explicit lock or a process shutdown.
pub(crate) fn serve(root: &Path, config: &[u8]) -> Result<(), String> {
    let mut key: SecretKey = Zeroizing::new([0u8; KEY_SIZE]);
    io::stdin().read_exact(&mut key[..]).map_err(|_| "missing private startup key")?;
    authenticate_config(config, &key)?;
    let path = directory(root)?.join(SOCK);
    let listener = UnixListener::bind(&path).map_err(|e| format!("cannot bind private credential socket: {e}"))?;
    fs::set_permissions(&path, fs::Permissions::from_mode(0o600))
        .map_err(|_| "cannot secure session socket")?;
    let mut stopping = false;
    for connection in listener.incoming() {
        let mut stream = match connection { Ok(s) => s, Err(_) => break };
        stream.set_read_timeout(Some(Duration::from_secs(120)))
            .map_err(|_| "cannot set agent inbound timeout")?;
        match transaction(&mut stream, config, &key) {
            Ok(stop) => stopping = stop,
            Err(message) => { let _ = reply(&mut stream, Err(message)); },
        }
        if stopping { break; }
    }
    drop(listener);
    let _ = fs::remove_file(&path);
    Ok(())
}
