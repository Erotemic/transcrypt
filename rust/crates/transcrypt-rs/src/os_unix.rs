//! The operating-system primitives outside `fsat.rs` that differ between
//! Unix and Windows (`os_windows.rs` has the same items): Git path bytes,
//! signals, process hardening, file privacy and the private agent's socket.

use std::{
    ffi::{OsStr, OsString},
    fs,
    io,
    os::{
        fd::AsRawFd,
        unix::{ffi::{OsStrExt, OsStringExt}, fs::{DirBuilderExt, FileTypeExt, MetadataExt, PermissionsExt}},
    },
    path::Path,
    time::Duration,
};

pub(crate) use std::os::unix::net::{UnixListener as Listener, UnixStream as Stream};

/// A Git path (raw bytes) as an OS path: any bytes but NUL are one on Unix.
pub(crate) fn os_string(bytes: &[u8]) -> Result<OsString, String> {
    Ok(OsString::from_vec(bytes.to_vec()))
}

/// Raw bytes of an OS path, as Git names it.
pub(crate) fn os_bytes(name: &OsStr) -> &[u8] {
    name.as_bytes()
}

/// Die quietly when a reader such as `head` closes our output, like other
/// command-line tools (Rust ignores SIGPIPE by default).
pub(crate) fn default_sigpipe() {
    // SAFETY: setting a signal disposition to its default is always valid.
    unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) };
}

/// Run `f` with SIGPIPE blocked in this thread, so that a write to a pipe
/// or socket whose reader is gone fails with EPIPE (an error that is
/// reported, and rolled back from) instead of killing the process: `main`
/// restores SIGPIPE's default so that `transcrypt-rs status | head` ends
/// quietly.
pub(crate) fn sigpipe_blocked<T>(f: impl FnOnce() -> T) -> T {
    // SAFETY: `sigset_t` is plain data, for which all zeroes is a valid
    // value; sigemptyset then initializes `pipe` as a set, and
    // pthread_sigmask changes only this thread's mask, saving it in
    // `previous`.
    let (pipe, previous) = unsafe {
        let (mut pipe, mut previous): (libc::sigset_t, libc::sigset_t) = (std::mem::zeroed(), std::mem::zeroed());
        libc::sigemptyset(&mut pipe);
        libc::sigaddset(&mut pipe, libc::SIGPIPE);
        libc::pthread_sigmask(libc::SIG_BLOCK, &pipe, &mut previous);
        (pipe, previous)
    };
    let result = f();
    // Discard a SIGPIPE raised meanwhile, then restore the mask.
    // SAFETY: sigpending fills the zeroed `pending`; sigwait returns at once
    // because the signal it waits for is pending (and blocked); `previous`
    // is the mask saved above.
    unsafe {
        let mut pending: libc::sigset_t = std::mem::zeroed();
        if libc::sigpending(&mut pending) == 0 && libc::sigismember(&pending, libc::SIGPIPE) == 1 {
            let mut signal = 0;
            libc::sigwait(&pipe, &mut signal);
        }
        libc::pthread_sigmask(libc::SIG_SETMASK, &previous, std::ptr::null_mut());
    }
    result
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

/// Keep `len` bytes at `ptr` out of swap where the OS allows it (best
/// effort: RLIMIT_MEMLOCK may forbid it).
pub(crate) fn lock_memory(ptr: *const u8, len: usize) {
    // SAFETY: the caller's pointer and length describe live memory.
    let _ = unsafe { libc::mlock(ptr.cast(), len) };
}

/// Close every descriptor inherited beyond stdio, so the long-lived agent
/// never keeps a caller's pipes, files or locks open.
pub(crate) fn close_inherited() {
    let fds: Vec<i32> = fs::read_dir("/dev/fd")
        .map(|dir| dir.filter_map(|e| e.ok()?.file_name().to_str()?.parse().ok()).collect())
        .unwrap_or_default();
    for fd in fds.into_iter().filter(|fd| *fd > 2) {
        // SAFETY: nothing in this process uses these descriptors yet; closing
        // an already closed one (the directory listing's own) is harmless.
        unsafe { libc::close(fd) };
    }
}

/// Whether the process `pid` still runs.
pub(crate) fn process_running(pid: u32) -> bool {
    let Ok(pid) = i32::try_from(pid) else { return false };
    // SAFETY: kill with signal 0 only checks whether the process exists.
    let alive = unsafe { libc::kill(pid, 0) } == 0;
    alive || io::Error::last_os_error().raw_os_error() == Some(libc::EPERM)
}

/// Whether files Git creates now are private to this user. Git creates
/// worktree files with mode `0666 & !umask`, and its filters inherit its
/// umask, so the smudge filter sees exactly the mask Git will apply.
pub(crate) fn checkouts_private() -> bool {
    // SAFETY: umask cannot fail and has no memory-safety preconditions. The
    // mask is process-wide, so it is put back at once; no other thread runs
    // at the callers (the smudge filter and `doctor`: `git.rs`'s helper
    // threads are scoped and joined), so none creates a file meanwhile.
    let previous = unsafe { libc::umask(0o077) };
    // SAFETY: as above.
    unsafe { libc::umask(previous) };
    previous & 0o077 == 0o077
}

/// How `doctor` describes `checkouts_private`.
pub(crate) const CHECKOUTS_PRIVATE: [&str; 2] = [
    "umask is permissive: Git checkouts write ciphertext; hooks or `hydrate` decrypt with mode 0600",
    "umask is private: Git checkouts write plaintext directly (mode 0600)",
];

/// Create a file that Git runs as a hook (executable on Unix).
pub(crate) fn create_hook(path: &Path) -> io::Result<fs::File> {
    use std::os::unix::fs::OpenOptionsExt;
    fs::OpenOptions::new().write(true).create_new(true).mode(0o700).open(path)
}

/// Make an existing hook file runnable; Git skips one that is not.
pub(crate) fn make_runnable(path: &Path) -> io::Result<()> {
    fs::set_permissions(path, fs::Permissions::from_mode(0o700))
}

/// Whether Git would run the hook file at `path`.
pub(crate) fn runnable(path: &Path) -> bool {
    fs::metadata(path).is_ok_and(|m| m.permissions().mode() & 0o111 != 0)
}

fn euid() -> u32 {
    // SAFETY: geteuid has no preconditions and cannot fail.
    unsafe { libc::geteuid() as u32 }
}

/// Whether `path` is a real directory (not a symlink) that only this user,
/// who owns it, can enter; `None` if it does not exist.
pub(crate) fn private_directory(path: &Path) -> io::Result<Option<bool>> {
    let meta = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    Ok(Some(meta.is_dir() && !meta.file_type().is_symlink() && meta.permissions().mode() & 0o077 == 0
        && meta.uid() == euid()))
}

/// Create a directory that only this user can enter.
pub(crate) fn create_private_directory(path: &Path) -> io::Result<()> {
    fs::DirBuilder::new().mode(0o700).create(path)
}

/// Whether `path` is a socket (not a symlink or another file); `None` if
/// nothing is there.
pub(crate) fn is_socket(path: &Path) -> io::Result<Option<bool>> {
    match fs::symlink_metadata(path) {
        Ok(meta) => Ok(Some(meta.file_type().is_socket())),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// Whether `path` is a socket that only this user, who owns it, can use.
pub(crate) fn private_socket(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_socket()
        && meta.permissions().mode() & 0o077 == 0 && meta.uid() == euid())
}

/// Restrict a just-bound socket to this user.
pub(crate) fn secure_socket(path: &Path) -> io::Result<()> {
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))
}

/// The effective UID of the process at the other end of a Unix socket, as
/// recorded by the kernel when the connection was made.
#[allow(clippy::unnecessary_cast)] // `uid_t` is not u32 everywhere.
fn peer_uid(stream: &Stream) -> io::Result<u32> {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    {
        // SAFETY: plain data, for which all zeroes is a valid value.
        let mut cred: libc::ucred = unsafe { std::mem::zeroed() };
        let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        // SAFETY: an open socket; `cred` and `len` describe a writable ucred buffer.
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

/// Whether the peer of `stream` runs as this user.
pub(crate) fn peer_is_this_user(stream: &Stream) -> bool {
    peer_uid(stream).is_ok_and(|uid| uid == euid())
}

/// Bound a stalled or broken peer (either end) instead of hanging forever.
pub(crate) fn set_timeouts(stream: &Stream, limit: Duration) -> io::Result<()> {
    stream.set_read_timeout(Some(limit)).and_then(|_| stream.set_write_timeout(Some(limit)))
}

/// The next client, or `None` once `idle` passes without one (or the
/// listener fails).
pub(crate) fn accept(listener: &Listener, idle: Option<Duration>) -> Option<Stream> {
    let idle_ms = idle.map_or(-1, |d| i32::try_from(d.as_millis()).unwrap_or(i32::MAX));
    loop {
        let mut ready = libc::pollfd { fd: listener.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one valid pollfd for the listener's open descriptor.
        match unsafe { libc::poll(&mut ready, 1, idle_ms) } {
            0 => return None,
            n if n < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted => continue,
            n if n < 0 => return None,
            _ => return listener.accept().ok().map(|(stream, _)| stream),
        }
    }
}

/// Nothing to do on Unix: the agent ignores the terminal it started from.
pub(crate) fn detach(_command: &mut std::process::Command) {}
