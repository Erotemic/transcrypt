//! The operating-system primitives outside `fsat_windows.rs` that differ
//! between Unix and Windows (`os_unix.rs` has the same items): Git path
//! bytes, process hardening, file privacy and the private agent's socket.
//!
//! Privacy is an owner-only access control list where Unix uses mode 0700
//! or 0600: a *protected* DACL (nothing inherited from the parent) whose
//! every grant is to this user. Administrators can take ownership of any
//! file, as root can read any file on Unix.

use std::{
    ffi::{OsStr, OsString},
    fs::{self, File},
    io::{self, Read, Write},
    mem::{size_of, zeroed},
    os::windows::{ffi::OsStrExt, fs::OpenOptionsExt, io::{AsRawHandle, FromRawHandle, OwnedHandle}},
    path::Path,
    ptr::{null, null_mut},
    sync::Once,
    time::Duration,
};
use windows_sys::{core::BOOL, Win32::{
    Foundation::{GetLastError, LocalFree, ERROR_ACCESS_DENIED, HANDLE, STILL_ACTIVE, WIN32_ERROR},
    Networking::WinSock::{
        accept as accept_socket, bind, closesocket, connect, listen, recv, send, setsockopt, socket, WSAGetLastError, WSAIoctl,
        WSAPoll, WSAStartup, AF_UNIX, INVALID_SOCKET, POLLRDNORM, SIO_AF_UNIX_GETPEERPID, SOCKADDR, SOCKADDR_UN,
        SOCKET, SOCKET_ERROR, SOCK_STREAM, SOL_SOCKET, SOMAXCONN, SO_RCVTIMEO, SO_SNDTIMEO, WSADATA, WSAPOLLFD,
    },
    Security::{
        Authorization::{
            ConvertSidToStringSidW, ConvertStringSecurityDescriptorToSecurityDescriptorW, GetSecurityInfo,
            SetSecurityInfo, SDDL_REVISION_1, SE_FILE_OBJECT,
        },
        EqualSid, GetAce, GetAclInformation, GetSecurityDescriptorControl, GetSecurityDescriptorDacl,
        GetTokenInformation, InitializeAcl, TokenOwner, TokenUser, AclSizeInformation, ACCESS_ALLOWED_ACE, ACL,
        ACL_REVISION, ACL_SIZE_INFORMATION, DACL_SECURITY_INFORMATION, OWNER_SECURITY_INFORMATION,
        PROTECTED_DACL_SECURITY_INFORMATION, PSECURITY_DESCRIPTOR, PSID, SECURITY_ATTRIBUTES, SE_DACL_PROTECTED,
        TOKEN_OWNER, TOKEN_QUERY, TOKEN_USER, UNPROTECTED_DACL_SECURITY_INFORMATION,
    },
    Storage::FileSystem::{
        CreateDirectoryW, GetFileInformationByHandleEx, FileAttributeTagInfo, FILE_ATTRIBUTE_DIRECTORY,
        FILE_ATTRIBUTE_REPARSE_POINT, FILE_ATTRIBUTE_TAG_INFO, FILE_FLAG_BACKUP_SEMANTICS,
        FILE_FLAG_OPEN_REPARSE_POINT, FILE_READ_ATTRIBUTES, READ_CONTROL, WRITE_DAC,
    },
    System::{
        Diagnostics::Debug::{SetErrorMode, SEM_FAILCRITICALERRORS, SEM_NOGPFAULTERRORBOX},
        Memory::VirtualLock,
        SystemServices::{ACCESS_ALLOWED_ACE_TYPE, ACCESS_DENIED_ACE_TYPE, IO_REPARSE_TAG_AF_UNIX},
        Threading::{GetCurrentProcess, GetExitCodeProcess, OpenProcess, OpenProcessToken, PROCESS_QUERY_LIMITED_INFORMATION},
    },
}};

/// The result of a call that returns a `BOOL` and sets the last error.
pub(crate) fn win32(ok: BOOL) -> io::Result<()> {
    if ok != 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
}

/// The result of a call that returns its error code.
pub(crate) fn status(code: WIN32_ERROR) -> io::Result<()> {
    if code == 0 { Ok(()) } else { Err(io::Error::from_raw_os_error(code as i32)) }
}

/// A Git path (raw bytes) as an OS path. Git for Windows names files in
/// UTF-8; other bytes cannot name a Windows file.
pub(crate) fn os_string(bytes: &[u8]) -> Result<OsString, String> {
    std::str::from_utf8(bytes).map(OsString::from).map_err(|_| "Git path is not UTF-8, which no Windows file name is".into())
}

/// Bytes of an OS path, as Git names it (UTF-8).
pub(crate) fn os_bytes(name: &OsStr) -> &[u8] {
    name.as_encoded_bytes()
}

/// Windows has no SIGPIPE: a write to a closed pipe fails with an error.
pub(crate) fn default_sigpipe() {}

/// Windows has no SIGPIPE: a write to a closed pipe already fails with an
/// error instead of ending the process.
pub(crate) fn sigpipe_blocked<T>(f: impl FnOnce() -> T) -> T {
    f()
}

/// Process hardening for every v3 process: no crash dialog (and so no
/// interactive crash report of its memory). Windows lets processes of the
/// same user read this one's memory; they are inside the trust boundary, as
/// on Unix.
pub(crate) fn harden_process() -> Result<(), String> {
    // SAFETY: SetErrorMode takes flags and returns the previous ones.
    unsafe { SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX) };
    Ok(())
}

/// Keep `len` bytes at `ptr` out of the page file where Windows allows it
/// (best effort).
pub(crate) fn lock_memory(ptr: *const u8, len: usize) {
    // SAFETY: the caller's pointer and length describe live memory.
    let _ = unsafe { VirtualLock(ptr.cast(), len) };
}

/// Nothing to close: Rust creates every handle non-inheritable, and the
/// agent is started with only its stdio.
pub(crate) fn close_inherited() {}

/// Whether the process `pid` still runs.
pub(crate) fn process_running(pid: u32) -> bool {
    // SAFETY: OpenProcess returns an owned handle or null.
    let process = unsafe { OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, 0, pid) };
    if process.is_null() {
        // Another user's process exists but cannot be opened.
        return unsafe { GetLastError() } == ERROR_ACCESS_DENIED;
    }
    // SAFETY: `process` is a fresh handle we own.
    let process = unsafe { OwnedHandle::from_raw_handle(process) };
    let mut code = 0u32;
    // SAFETY: valid process handle and out-pointer.
    let ok = unsafe { GetExitCodeProcess(process.as_raw_handle(), &mut code) } != 0;
    ok && code == STILL_ACTIVE as u32
}

/// Whether files Git creates now are private to this user: never on
/// Windows, where they take the access their directory gives (the private
/// mode then keeps ciphertext until `hydrate` writes owner-only files).
pub(crate) fn checkouts_private() -> bool {
    false
}

/// How `doctor` describes `checkouts_private`.
pub(crate) const CHECKOUTS_PRIVATE: [&str; 2] = [
    "Git checkouts write ciphertext; hooks or `hydrate` decrypt as files only this user can open",
    "Git checkouts write plaintext directly",
];

/// Create a file that Git runs as a hook (Git for Windows runs any file).
pub(crate) fn create_hook(path: &Path) -> io::Result<File> {
    fs::OpenOptions::new().write(true).create_new(true).open(path)
}

/// Hooks need no execute permission on Windows.
pub(crate) fn make_runnable(_path: &Path) -> io::Result<()> {
    Ok(())
}

/// Whether Git would run the hook file at `path`.
pub(crate) fn runnable(path: &Path) -> bool {
    path.is_file()
}

/// A buffer that `LocalFree` releases (what the security APIs return).
struct Local(*mut core::ffi::c_void);

impl Drop for Local {
    fn drop(&mut self) {
        // SAFETY: the pointer was allocated by the API that returned it.
        unsafe { LocalFree(self.0) };
    }
}

/// `TOKEN_USER` or `TOKEN_OWNER` of a process (a handle with
/// `PROCESS_QUERY_LIMITED_INFORMATION`), in an aligned buffer.
fn token_information(process: HANDLE, class: i32) -> io::Result<Vec<u64>> {
    let mut token: HANDLE = null_mut();
    // SAFETY: a valid process handle; `token` receives a handle we own.
    win32(unsafe { OpenProcessToken(process, TOKEN_QUERY, &mut token) })?;
    // SAFETY: `token` is a fresh handle that nothing else owns.
    let token = unsafe { OwnedHandle::from_raw_handle(token) };
    let mut size = 0u32;
    // SAFETY: a size query with no buffer.
    unsafe { GetTokenInformation(token.as_raw_handle(), class, null_mut(), 0, &mut size) };
    let mut buffer = vec![0u64; (size as usize).div_ceil(8)];
    // SAFETY: the buffer holds `size` bytes.
    win32(unsafe { GetTokenInformation(token.as_raw_handle(), class, buffer.as_mut_ptr().cast(), size, &mut size) })?;
    Ok(buffer)
}

/// This process's user SID, and the default owner of objects it creates
/// (for an elevated administrator, the Administrators group).
struct Identity {
    user: Vec<u64>,
    owner: Vec<u64>,
}

impl Identity {
    fn current() -> io::Result<Identity> {
        // SAFETY: returns the pseudo-handle of this process, which needs no closing.
        let process = unsafe { GetCurrentProcess() };
        Ok(Identity { user: token_information(process, TokenUser)?, owner: token_information(process, TokenOwner)? })
    }

    fn user(&self) -> PSID {
        // SAFETY: the buffer holds a TOKEN_USER, whose SID points into it.
        unsafe { (*self.user.as_ptr().cast::<TOKEN_USER>()).User.Sid }
    }

    fn owner(&self) -> PSID {
        // SAFETY: the buffer holds a TOKEN_OWNER, whose SID points into it.
        unsafe { (*self.owner.as_ptr().cast::<TOKEN_OWNER>()).Owner }
    }

    /// The SDDL of a protected DACL that grants this user, and nobody
    /// else, full access to the object and (inherited) its children.
    fn private_sddl(&self) -> io::Result<Vec<u16>> {
        let mut text: *mut u16 = null_mut();
        // SAFETY: the SID is valid; `text` receives a LocalAlloc'd string.
        win32(unsafe { ConvertSidToStringSidW(self.user(), &mut text) })?;
        let _free = Local(text.cast());
        // SAFETY: a NUL-terminated wide string.
        let sid = unsafe { std::slice::from_raw_parts(text, (0..).take_while(|&i| *text.add(i) != 0).count()) };
        Ok("D:P(A;OICI;FA;;;".encode_utf16().chain(sid.iter().copied()).chain(")\0".encode_utf16()).collect())
    }
}

/// A self-relative security descriptor whose DACL only this user is in.
pub(crate) struct PrivateDescriptor(Local);

impl PrivateDescriptor {
    pub(crate) fn new() -> io::Result<PrivateDescriptor> {
        let sddl = Identity::current()?.private_sddl()?;
        let mut descriptor: PSECURITY_DESCRIPTOR = null_mut();
        // SAFETY: a NUL-terminated SDDL string; the descriptor is LocalAlloc'd.
        win32(unsafe { ConvertStringSecurityDescriptorToSecurityDescriptorW(sddl.as_ptr(), SDDL_REVISION_1, &mut descriptor, null_mut()) })?;
        Ok(PrivateDescriptor(Local(descriptor)))
    }

    pub(crate) fn as_ptr(&self) -> PSECURITY_DESCRIPTOR {
        self.0 .0
    }

    fn dacl(&self) -> io::Result<*mut ACL> {
        let (mut present, mut defaulted, mut dacl) = (0, 0, null_mut());
        // SAFETY: a valid descriptor and out-pointers.
        if unsafe { GetSecurityDescriptorDacl(self.as_ptr(), &mut present, &mut dacl, &mut defaulted) } == 0 || present == 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(dacl)
    }
}

/// Restrict an open file or directory (opened with `WRITE_DAC`) to this
/// user, replacing whatever its DACL granted (like chmod 0600 or 0700).
pub(crate) fn set_private(handle: HANDLE) -> io::Result<()> {
    let descriptor = PrivateDescriptor::new()?;
    let dacl = descriptor.dacl()?;
    // SAFETY: a valid handle and the descriptor's DACL.
    status(unsafe {
        SetSecurityInfo(handle, SE_FILE_OBJECT, DACL_SECURITY_INFORMATION | PROTECTED_DACL_SECURITY_INFORMATION,
            null_mut(), null_mut(), dacl, null())
    })
}

/// Give an open file (opened with `WRITE_DAC`) only the access its
/// directory passes on, as a file that Git creates there has.
pub(crate) fn set_inherited(handle: HANDLE) -> io::Result<()> {
    // SAFETY: plain data, for which all zeroes is a valid value.
    let mut empty: ACL = unsafe { zeroed() };
    // SAFETY: `empty` is large enough for an ACL without entries.
    win32(unsafe { InitializeAcl(&mut empty, size_of::<ACL>() as u32, ACL_REVISION) })?;
    // SAFETY: a valid handle and ACL.
    status(unsafe {
        SetSecurityInfo(handle, SE_FILE_OBJECT, DACL_SECURITY_INFORMATION | UNPROTECTED_DACL_SECURITY_INFORMATION,
            null_mut(), null_mut(), &empty, null())
    })
}

/// Whether only this user can use an open object (opened with
/// `READ_CONTROL`): it belongs to this user, its DACL is protected (nothing
/// inherited), and every grant in it is to this user.
pub(crate) fn is_private(handle: HANDLE) -> io::Result<bool> {
    let identity = Identity::current()?;
    let (mut owner, mut dacl, mut descriptor): (PSID, *mut ACL, PSECURITY_DESCRIPTOR) = (null_mut(), null_mut(), null_mut());
    // SAFETY: a valid handle; the descriptor is LocalAlloc'd and owns `owner` and `dacl`.
    status(unsafe {
        GetSecurityInfo(handle, SE_FILE_OBJECT, OWNER_SECURITY_INFORMATION | DACL_SECURITY_INFORMATION,
            &mut owner, null_mut(), &mut dacl, null_mut(), &mut descriptor)
    })?;
    let _free = Local(descriptor);
    let (mut control, mut revision) = (0u16, 0u32);
    // SAFETY: valid descriptor and out-pointers.
    win32(unsafe { GetSecurityDescriptorControl(descriptor, &mut control, &mut revision) })?;
    // SAFETY: valid SIDs.
    let owned = unsafe { EqualSid(owner, identity.user()) != 0 || EqualSid(owner, identity.owner()) != 0 };
    // A null DACL grants everyone everything.
    if !owned || control & SE_DACL_PROTECTED == 0 || dacl.is_null() { return Ok(false); }
    // SAFETY: plain data, for which all zeroes is a valid value.
    let mut size: ACL_SIZE_INFORMATION = unsafe { zeroed() };
    // SAFETY: a valid ACL and a buffer of the requested class.
    win32(unsafe { GetAclInformation(dacl, (&mut size as *mut ACL_SIZE_INFORMATION).cast(), size_of::<ACL_SIZE_INFORMATION>() as u32, AclSizeInformation) })?;
    for index in 0..size.AceCount {
        let mut ace = null_mut();
        // SAFETY: `index` is below the ACL's entry count.
        win32(unsafe { GetAce(dacl, index, &mut ace) })?;
        let ace = ace.cast::<ACCESS_ALLOWED_ACE>();
        // SAFETY: every ACE starts with its header; an access-allowed ACE
        // holds its SID at `SidStart`. Deny entries take nothing away from
        // privacy; any other kind of grant is not understood here.
        let kind = unsafe { (*ace).Header.AceType } as u32;
        if kind == ACCESS_ALLOWED_ACE_TYPE {
            if unsafe { EqualSid(std::ptr::addr_of_mut!((*ace).SidStart).cast(), identity.user()) } == 0 {
                return Ok(false);
            }
        } else if kind != ACCESS_DENIED_ACE_TYPE {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Open `path` itself (a symlink, junction or socket is not followed).
fn open_entry(path: &Path, access: u32) -> io::Result<File> {
    fs::OpenOptions::new().access_mode(access)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT).open(path)
}

/// The attributes and reparse tag of an open file.
pub(crate) fn attribute_tag(handle: HANDLE) -> io::Result<(u32, u32)> {
    // SAFETY: plain data, for which all zeroes is a valid value.
    let mut info: FILE_ATTRIBUTE_TAG_INFO = unsafe { zeroed() };
    // SAFETY: a valid handle and a buffer of the requested class.
    win32(unsafe { GetFileInformationByHandleEx(handle, FileAttributeTagInfo, (&mut info as *mut FILE_ATTRIBUTE_TAG_INFO).cast(), size_of::<FILE_ATTRIBUTE_TAG_INFO>() as u32) })?;
    Ok((info.FileAttributes, info.ReparseTag))
}

/// Whether `path` is a real directory (not a symlink or junction) that only
/// this user, who owns it, can enter; `None` if it does not exist.
pub(crate) fn private_directory(path: &Path) -> io::Result<Option<bool>> {
    let entry = match open_entry(path, FILE_READ_ATTRIBUTES | READ_CONTROL) {
        Ok(entry) => entry,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let (attributes, _) = attribute_tag(entry.as_raw_handle())?;
    let directory = attributes & FILE_ATTRIBUTE_DIRECTORY != 0 && attributes & FILE_ATTRIBUTE_REPARSE_POINT == 0;
    Ok(Some(directory && is_private(entry.as_raw_handle())?))
}

/// Create a directory that only this user can enter (created so, never
/// briefly open to others).
pub(crate) fn create_private_directory(path: &Path) -> io::Result<()> {
    let descriptor = PrivateDescriptor::new()?;
    let attributes = SECURITY_ATTRIBUTES {
        nLength: size_of::<SECURITY_ATTRIBUTES>() as u32,
        lpSecurityDescriptor: descriptor.as_ptr(),
        bInheritHandle: 0,
    };
    let wide: Vec<u16> = path.as_os_str().encode_wide().chain([0]).collect();
    // SAFETY: a NUL-terminated path and valid security attributes.
    win32(unsafe { CreateDirectoryW(wide.as_ptr(), &attributes) })
}

/// Whether `path` is a socket (Windows marks the file of a Unix-domain
/// socket with its own reparse tag); `None` if nothing is there.
pub(crate) fn is_socket(path: &Path) -> io::Result<Option<bool>> {
    match open_entry(path, FILE_READ_ATTRIBUTES) {
        Ok(entry) => Ok(Some(attribute_tag(entry.as_raw_handle())?.1 == IO_REPARSE_TAG_AF_UNIX)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// Whether `path` is a socket that only this user, who owns it, can use.
pub(crate) fn private_socket(path: &Path) -> bool {
    matches!(is_socket(path), Ok(Some(true)))
        && open_entry(path, FILE_READ_ATTRIBUTES | READ_CONTROL).is_ok_and(|e| is_private(e.as_raw_handle()).unwrap_or(false))
}

/// Restrict a just-bound socket to this user.
pub(crate) fn secure_socket(path: &Path) -> io::Result<()> {
    set_private(open_entry(path, WRITE_DAC | READ_CONTROL)?.as_raw_handle())
}

fn startup() {
    static STARTED: Once = Once::new();
    STARTED.call_once(|| {
        // SAFETY: plain data, for which all zeroes is a valid value.
        let mut data: WSADATA = unsafe { zeroed() };
        // SAFETY: version 2.2 and a valid out-pointer; never cleaned up.
        unsafe { WSAStartup(0x0202, &mut data) };
    });
}

fn socket_error() -> io::Error {
    // SAFETY: no preconditions.
    io::Error::from_raw_os_error(unsafe { WSAGetLastError() })
}

/// A Unix-domain socket (`AF_UNIX`, Windows 10 1803 and later).
struct Socket(SOCKET);

impl Drop for Socket {
    fn drop(&mut self) {
        // SAFETY: we own the socket.
        unsafe { closesocket(self.0) };
    }
}

impl Socket {
    fn new() -> io::Result<Socket> {
        startup();
        // SAFETY: creating a socket has no preconditions.
        let s = unsafe { socket(AF_UNIX as i32, SOCK_STREAM, 0) };
        if s == INVALID_SOCKET { Err(socket_error()) } else { Ok(Socket(s)) }
    }

    /// The address of `path` (relative to the current directory).
    fn address(path: &Path) -> io::Result<SOCKADDR_UN> {
        let mut address = SOCKADDR_UN { sun_family: AF_UNIX, sun_path: [0; 108] };
        let bytes = path.to_str().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "socket path is not Unicode"))?.as_bytes();
        if bytes.len() >= address.sun_path.len() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "socket path too long"));
        }
        for (slot, byte) in address.sun_path.iter_mut().zip(bytes) { *slot = *byte as i8; }
        Ok(address)
    }

    fn check(rc: i32) -> io::Result<()> {
        if rc == SOCKET_ERROR { Err(socket_error()) } else { Ok(()) }
    }
}

/// A connection to or from the agent.
pub(crate) struct Stream(Socket);

/// The agent's listening socket.
pub(crate) struct Listener(Socket);

impl Stream {
    pub(crate) fn connect(path: impl AsRef<Path>) -> io::Result<Stream> {
        let socket = Socket::new()?;
        let address = Socket::address(path.as_ref())?;
        // SAFETY: a valid socket and address of the given size.
        Socket::check(unsafe { connect(socket.0, (&address as *const SOCKADDR_UN).cast::<SOCKADDR>(), size_of::<SOCKADDR_UN>() as i32) })?;
        Ok(Stream(socket))
    }
}

impl Listener {
    pub(crate) fn bind(path: impl AsRef<Path>) -> io::Result<Listener> {
        let socket = Socket::new()?;
        let address = Socket::address(path.as_ref())?;
        // SAFETY: a valid socket and address of the given size.
        Socket::check(unsafe { bind(socket.0, (&address as *const SOCKADDR_UN).cast::<SOCKADDR>(), size_of::<SOCKADDR_UN>() as i32) })?;
        // SAFETY: a bound socket.
        Socket::check(unsafe { listen(socket.0, SOMAXCONN as i32) })?;
        Ok(Listener(socket))
    }
}

impl Read for Stream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let len = i32::try_from(buf.len()).unwrap_or(i32::MAX);
        // SAFETY: the buffer holds at least `len` bytes.
        let n = unsafe { recv(self.0 .0, buf.as_mut_ptr(), len, 0) };
        if n == SOCKET_ERROR { Err(socket_error()) } else { Ok(n as usize) }
    }
}

impl Write for Stream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let len = i32::try_from(buf.len()).unwrap_or(i32::MAX);
        // SAFETY: the buffer holds at least `len` bytes.
        let n = unsafe { send(self.0 .0, buf.as_ptr(), len, 0) };
        if n == SOCKET_ERROR { Err(socket_error()) } else { Ok(n as usize) }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The process at the other end of a connection, as Windows recorded it.
fn peer_process(stream: &Stream) -> io::Result<u32> {
    let (mut pid, mut returned) = (0u32, 0u32);
    // SAFETY: a connected socket and a 4-byte output buffer.
    let rc = unsafe {
        WSAIoctl(stream.0 .0, SIO_AF_UNIX_GETPEERPID, null(), 0, (&mut pid as *mut u32).cast(), 4, &mut returned, null_mut(), None)
    };
    Socket::check(rc).map(|_| pid)
}

/// Whether the process at the other end of `stream` runs as this user. The
/// private directory already keeps other users from connecting.
pub(crate) fn peer_is_this_user(stream: &Stream) -> bool {
    let check = || -> io::Result<bool> {
        let pid = peer_process(stream)?;
        // SAFETY: OpenProcess returns an owned handle or null.
        let process = unsafe { OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, 0, pid) };
        if process.is_null() { return Err(io::Error::last_os_error()); }
        // SAFETY: a fresh handle that nothing else owns.
        let process = unsafe { OwnedHandle::from_raw_handle(process) };
        let buffer = token_information(process.as_raw_handle(), TokenUser)?;
        // SAFETY: the buffer holds a TOKEN_USER.
        let peer = unsafe { (*buffer.as_ptr().cast::<TOKEN_USER>()).User.Sid };
        // SAFETY: valid SIDs.
        Ok(unsafe { EqualSid(peer, Identity::current()?.user()) } != 0)
    };
    check().unwrap_or(false)
}

/// Bound a stalled or broken peer (either end) instead of hanging forever.
pub(crate) fn set_timeouts(stream: &Stream, limit: Duration) -> io::Result<()> {
    let ms = u32::try_from(limit.as_millis()).unwrap_or(u32::MAX);
    for option in [SO_RCVTIMEO, SO_SNDTIMEO] {
        // SAFETY: a valid socket and a 4-byte option value.
        Socket::check(unsafe { setsockopt(stream.0 .0, SOL_SOCKET, option, (&ms as *const u32).cast(), 4) })?;
    }
    Ok(())
}

/// The next client, or `None` once `idle` passes without one (or the
/// listener fails).
pub(crate) fn accept(listener: &Listener, idle: Option<Duration>) -> Option<Stream> {
    let idle_ms = idle.map_or(-1, |d| i32::try_from(d.as_millis()).unwrap_or(i32::MAX));
    let mut ready = WSAPOLLFD { fd: listener.0 .0, events: POLLRDNORM, revents: 0 };
    // SAFETY: one valid poll entry.
    if unsafe { WSAPoll(&mut ready, 1, idle_ms) } <= 0 { return None; }
    // SAFETY: a listening socket; the peer address is not wanted.
    let s = unsafe { accept_socket(listener.0 .0, null_mut(), null_mut()) };
    if s == INVALID_SOCKET { None } else { Some(Stream(Socket(s))) }
}

/// Start the agent detached: alive when the console that started it closes,
/// and holding none of this process's standard handles. Windows passes every
/// inheritable handle to a child, and a caller waiting for the end of this
/// process's output (`git`, a test) would otherwise wait for the agent too.
/// The child still gets its own standard handles, which Rust makes for it.
pub(crate) fn detach(command: &mut std::process::Command) {
    use std::os::windows::process::CommandExt;
    use windows_sys::Win32::{
        Foundation::{SetHandleInformation, HANDLE_FLAG_INHERIT},
        System::{
            Console::{GetStdHandle, STD_ERROR_HANDLE, STD_INPUT_HANDLE, STD_OUTPUT_HANDLE},
            Threading::{CREATE_NEW_PROCESS_GROUP, DETACHED_PROCESS},
        },
    };
    for which in [STD_INPUT_HANDLE, STD_OUTPUT_HANDLE, STD_ERROR_HANDLE] {
        // SAFETY: clearing a flag of this process's own standard handle.
        unsafe { SetHandleInformation(GetStdHandle(which), HANDLE_FLAG_INHERIT, 0) };
    }
    command.creation_flags(DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP);
}
