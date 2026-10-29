//! Directory-fd relative filesystem operations for protected worktree files.
//!
//! Every protected path is resolved once, component by component, with
//! `openat(O_NOFOLLOW | O_DIRECTORY)`, and all later reads, staging writes and
//! renames are relative to the held directory descriptors. A concurrent
//! process that swaps a parent directory for a symlink after resolution can
//! no longer redirect a write outside the repository. This narrows, but does
//! not eliminate, same-UID races: such a process can still change a file's
//! contents between our read and our rename.

use crate::modes::{GROUP_OTHER_BITS, OWNER_BITS, PERMISSION_BITS};
use std::{
    ffi::{CStr, CString, OsStr, OsString},
    fs::File,
    io,
    os::{
        fd::{AsRawFd, FromRawFd, OwnedFd},
        unix::{ffi::{OsStrExt, OsStringExt}, fs::{MetadataExt, PermissionsExt}},
    },
    path::Path,
};

fn cstr(name: &OsStr) -> io::Result<CString> {
    CString::new(name.as_bytes()).map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "NUL in path"))
}

/// One path component (no separator, no NUL), as every name-taking `Dir`
/// operation needs, so that none can reach outside the held directory.
fn component(name: &OsStr) -> io::Result<CString> {
    if name.is_empty() || name.as_bytes().contains(&b'/') {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "not a single path component"));
    }
    cstr(name)
}

/// Set this thread's errno.
fn set_errno(value: libc::c_int) {
    // SAFETY: each returns a pointer to the calling thread's errno.
    unsafe {
        #[cfg(any(target_os = "linux", target_os = "android"))]
        { *libc::__errno_location() = value; }
        #[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd", target_os = "dragonfly"))]
        { *libc::__error() = value; }
        #[cfg(any(target_os = "netbsd", target_os = "openbsd"))]
        { *libc::__errno() = value; }
    }
}

fn check(rc: libc::c_int) -> io::Result<libc::c_int> {
    if rc < 0 { Err(io::Error::last_os_error()) } else { Ok(rc) }
}

fn fstat(fd: &impl AsRawFd) -> io::Result<libc::stat> {
    // SAFETY: `stat` is plain data, for which all zeroes is a valid value.
    let mut st: libc::stat = unsafe { std::mem::zeroed() };
    // SAFETY: an open descriptor and a writable `stat`.
    check(unsafe { libc::fstat(fd.as_raw_fd(), &mut st) })?;
    Ok(st)
}

/// Identity, size and modification time of a file. Writing, truncating or
/// replacing a file changes its stamp, so comparing stamps just before a
/// rename detects that the file changed since it was checked. Not ctime:
/// FreeBSD's soft updates change a renamed file's ctime asynchronously,
/// when they finish removing its old name, well after the rename returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Stamp([i64; 5]);

impl Stamp {
    // The field types differ between platforms (Linux, macOS).
    #[allow(clippy::unnecessary_cast)]
    fn from_stat(st: &libc::stat) -> Stamp {
        #[cfg(target_os = "netbsd")]
        let mtime_nsec = st.st_mtimensec;
        #[cfg(not(target_os = "netbsd"))]
        let mtime_nsec = st.st_mtime_nsec;
        Stamp([st.st_dev as i64, st.st_ino as i64, st.st_size as i64, st.st_mtime as i64, mtime_nsec as i64])
    }

    /// The stamp of an open file.
    pub(crate) fn of(file: &File) -> io::Result<Stamp> {
        fstat(file).map(|st| Stamp::from_stat(&st))
    }
}

/// Permissions for a replacement file (`Dir::replacement_mode`).
#[derive(Clone, Copy)]
pub(crate) struct Mode(u32);

/// Give a (new, still private) replacement file its permissions.
pub(crate) fn set_mode(file: &File, mode: Mode) -> io::Result<()> {
    file.set_permissions(std::fs::Permissions::from_mode(mode.0))
}

/// The number of hard links to an open file.
pub(crate) fn links(file: &File) -> io::Result<u64> {
    #[allow(clippy::useless_conversion)] // `nlink` is u64 on most, not all, platforms.
    Ok(u64::from(file.metadata()?.nlink()))
}

/// An open directory.
pub(crate) struct Dir(OwnedFd);

impl Dir {
    /// Open a directory by path (the trusted repository root).
    pub(crate) fn open(path: &Path) -> io::Result<Dir> {
        let name = cstr(path.as_os_str())?;
        // SAFETY: `name` is NUL-terminated and outlives the call.
        let fd = check(unsafe { libc::open(name.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC) })?;
        // SAFETY: `fd` is a fresh descriptor that nothing else owns.
        Ok(Dir(unsafe { OwnedFd::from_raw_fd(fd) }))
    }

    fn openat(&self, name: &OsStr, flags: libc::c_int, mode: u32) -> io::Result<OwnedFd> {
        let c = component(name)?;
        // SAFETY: an open directory descriptor and a NUL-terminated name;
        // the variadic mode is passed as the C `unsigned int` it promotes to.
        let fd = check(unsafe {
            libc::openat(self.0.as_raw_fd(), c.as_ptr(), flags | libc::O_NOFOLLOW | libc::O_CLOEXEC, mode as libc::c_uint)
        })?;
        // SAFETY: `fd` is a fresh descriptor that nothing else owns.
        Ok(unsafe { OwnedFd::from_raw_fd(fd) })
    }

    /// A subdirectory; fails if `name` is a symlink or not a directory.
    pub(crate) fn subdir(&self, name: &OsStr) -> io::Result<Dir> {
        self.openat(name, libc::O_RDONLY | libc::O_DIRECTORY, 0).map(Dir)
    }

    /// Open `name` for reading; fails on symlinks and non-regular files.
    pub(crate) fn open_regular(&self, name: &OsStr) -> io::Result<File> {
        let file = File::from(self.openat(name, libc::O_RDONLY | libc::O_NONBLOCK, 0)?);
        if !file.metadata()?.is_file() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "not a regular file"));
        }
        Ok(file)
    }

    /// Exclusively create a new regular file.
    pub(crate) fn create_new(&self, name: &OsStr, mode: u32) -> io::Result<File> {
        self.openat(name, libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL, mode).map(File::from)
    }

    /// Create a directory; one that already exists (whatever it is) is not
    /// an error: open it with `subdir`, which refuses anything else.
    pub(crate) fn mkdir(&self, name: &OsStr, mode: u32) -> io::Result<()> {
        let c = component(name)?;
        // SAFETY: an open directory descriptor and a NUL-terminated name.
        match check(unsafe { libc::mkdirat(self.0.as_raw_fd(), c.as_ptr(), mode as libc::mode_t) }) {
            Err(e) if e.kind() != io::ErrorKind::AlreadyExists => Err(e),
            _ => Ok(()),
        }
    }

    /// Atomically rename `from` in this directory to `to` in `to_dir`.
    pub(crate) fn rename_to(&self, from: &OsStr, to_dir: &Dir, to: &OsStr) -> io::Result<()> {
        let (f, t) = (component(from)?, component(to)?);
        // SAFETY: open directory descriptors and NUL-terminated names.
        check(unsafe { libc::renameat(self.0.as_raw_fd(), f.as_ptr(), to_dir.0.as_raw_fd(), t.as_ptr()) }).map(|_| ())
    }

    pub(crate) fn unlink(&self, name: &OsStr) -> io::Result<()> {
        let c = component(name)?;
        // SAFETY: an open directory descriptor and a NUL-terminated name.
        check(unsafe { libc::unlinkat(self.0.as_raw_fd(), c.as_ptr(), 0) }).map(|_| ())
    }

    fn lstat(&self, name: &OsStr) -> io::Result<libc::stat> {
        let c = component(name)?;
        // SAFETY: `stat` is plain data, for which all zeroes is a valid value.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        // SAFETY: an open directory descriptor, a NUL-terminated name and a
        // writable `stat`.
        check(unsafe { libc::fstatat(self.0.as_raw_fd(), c.as_ptr(), &mut st, libc::AT_SYMLINK_NOFOLLOW) })?;
        Ok(st)
    }

    /// `lstat` of an entry: (is regular file, is symlink).
    pub(crate) fn entry_kind(&self, name: &OsStr) -> io::Result<(bool, bool)> {
        let kind = self.lstat(name)?.st_mode & libc::S_IFMT;
        Ok((kind == libc::S_IFREG, kind == libc::S_IFLNK))
    }

    /// The permissions for a file replacing the entry `name` (not followed
    /// if a symlink): its own, restricted to this user when `private`.
    #[allow(clippy::unnecessary_cast)] // `mode_t` is u16 on macOS.
    pub(crate) fn replacement_mode(&self, name: &OsStr, private: bool) -> io::Result<Mode> {
        let mode = self.lstat(name)?.st_mode as u32;
        Ok(Mode(if private { mode & OWNER_BITS } else { mode & PERMISSION_BITS }))
    }

    /// After `name` was renamed into this directory with the permissions
    /// `set_mode` gave it: make the rename durable.
    pub(crate) fn finish_replace(&self, _name: &OsStr, _mode: Mode) -> io::Result<()> {
        self.sync()
    }

    /// Remove group and other permissions from the regular file `name`
    /// (through an `O_NOFOLLOW` descriptor, so a swapped-in symlink is
    /// never followed).
    pub(crate) fn make_private(&self, name: &OsStr) -> io::Result<()> {
        let file = self.open_regular(name)?;
        let mode = file.metadata()?.permissions().mode();
        if mode & GROUP_OTHER_BITS != 0 {
            file.set_permissions(std::fs::Permissions::from_mode(mode & OWNER_BITS))?;
        }
        Ok(())
    }

    /// The stamp of an entry, without following a symlink.
    pub(crate) fn stamp(&self, name: &OsStr) -> io::Result<Stamp> {
        self.lstat(name).map(|st| Stamp::from_stat(&st))
    }

    /// Whether only this directory's owner can enter it.
    #[allow(clippy::unnecessary_cast)] // `mode_t` is u16 on macOS.
    pub(crate) fn is_private(&self) -> io::Result<bool> {
        Ok(fstat(&self.0)?.st_mode as u32 & GROUP_OTHER_BITS == 0)
    }

    /// Names of the entries of this directory (excluding `.` and `..`). A
    /// read error is an error, never a shorter listing (callers purge what
    /// they list).
    pub(crate) fn entries(&self) -> io::Result<Vec<OsString>> {
        // SAFETY: duplicating an open descriptor; the duplicate is ours.
        let dup = check(unsafe { libc::fcntl(self.0.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 0) })?;
        // SAFETY: `dup` is an open directory descriptor; on success the
        // stream owns it, on failure we still do.
        let stream = unsafe { libc::fdopendir(dup) };
        if stream.is_null() {
            let err = io::Error::last_os_error();
            // SAFETY: `dup` is ours and not used again.
            unsafe { libc::close(dup) };
            return Err(err);
        }
        // SAFETY: a valid DIR*. The duplicate shares its read position with
        // this directory's descriptor, so start from the beginning.
        unsafe { libc::rewinddir(stream) };
        let mut names = Vec::new();
        let result = loop {
            // readdir returns null both at the end and on an error; only
            // errno tells them apart.
            set_errno(0);
            // SAFETY: `stream` is a valid DIR*.
            let entry = unsafe { libc::readdir(stream) };
            if entry.is_null() {
                let err = io::Error::last_os_error();
                break if err.raw_os_error() == Some(0) { Ok(names) } else { Err(err) };
            }
            // SAFETY: `d_name` is NUL-terminated and valid until the next
            // readdir; it is copied before then.
            let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
            if name != b"." && name != b".." {
                names.push(OsString::from_vec(name.to_vec()));
            }
        };
        // SAFETY: `stream` is open and not used again; this also closes `dup`.
        unsafe { libc::closedir(stream) };
        result
    }

    /// Take an exclusive advisory lock on this directory without waiting;
    /// it is released when the descriptor is closed (also on a crash).
    pub(crate) fn try_lock(&self) -> io::Result<()> {
        // SAFETY: an open descriptor; flock takes integer arguments only.
        check(unsafe { libc::flock(self.0.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) }).map(|_| ())
    }

    pub(crate) fn sync(&self) -> io::Result<()> {
        // SAFETY: an open descriptor.
        check(unsafe { libc::fsync(self.0.as_raw_fd()) }).map(|_| ())
    }
}
