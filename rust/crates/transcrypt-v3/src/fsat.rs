//! Directory-fd relative filesystem operations for protected worktree files.
//!
//! Every protected path is resolved once, component by component, with
//! `openat(O_NOFOLLOW | O_DIRECTORY)`, and all later reads, staging writes and
//! renames are relative to the held directory descriptors. A concurrent
//! process that swaps a parent directory for a symlink after resolution can
//! no longer redirect a write outside the repository. This narrows, but does
//! not eliminate, same-UID races: such a process can still change a file's
//! contents between our read and our rename.

use std::{
    ffi::{CStr, CString, OsStr, OsString},
    fs::File,
    io,
    os::{
        fd::{AsRawFd, FromRawFd, OwnedFd},
        unix::ffi::{OsStrExt, OsStringExt},
    },
    path::Path,
};

fn cstr(name: &OsStr) -> io::Result<CString> {
    CString::new(name.as_bytes()).map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "NUL in path"))
}

fn check(rc: libc::c_int) -> io::Result<libc::c_int> {
    if rc < 0 { Err(io::Error::last_os_error()) } else { Ok(rc) }
}

/// Identity, size and change times of a file. Writing, truncating, replacing
/// or chmod-ing a file changes its stamp, so comparing stamps just before a
/// rename detects that the file changed since it was checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Stamp([i64; 7]);

impl Stamp {
    fn from_stat(st: &libc::stat) -> Stamp {
        Stamp([
            st.st_dev as i64, st.st_ino as i64, st.st_size as i64,
            st.st_mtime as i64, st.st_mtime_nsec as i64,
            st.st_ctime as i64, st.st_ctime_nsec as i64,
        ])
    }

    /// The stamp of an open file.
    pub(crate) fn of(file: &File) -> io::Result<Stamp> {
        // SAFETY: `st` is fully written by a successful fstat.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        check(unsafe { libc::fstat(file.as_raw_fd(), &mut st) })?;
        Ok(Stamp::from_stat(&st))
    }
}

/// An open directory.
pub(crate) struct Dir(OwnedFd);

impl Dir {
    /// Open a directory by path (the trusted repository root).
    pub(crate) fn open(path: &Path) -> io::Result<Dir> {
        let name = cstr(path.as_os_str())?;
        // SAFETY: `name` is a valid NUL-terminated string; the returned fd is owned.
        let fd = check(unsafe { libc::open(name.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC) })?;
        // SAFETY: `fd` is a fresh descriptor we own.
        Ok(Dir(unsafe { OwnedFd::from_raw_fd(fd) }))
    }

    fn openat(&self, name: &OsStr, flags: libc::c_int, mode: libc::mode_t) -> io::Result<OwnedFd> {
        if name.is_empty() || name.as_bytes().contains(&b'/') {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "not a single path component"));
        }
        let c = cstr(name)?;
        // SAFETY: valid dirfd and NUL-terminated name; the returned fd is owned.
        let fd = check(unsafe {
            libc::openat(self.0.as_raw_fd(), c.as_ptr(), flags | libc::O_NOFOLLOW | libc::O_CLOEXEC, mode as libc::c_uint)
        })?;
        // SAFETY: `fd` is a fresh descriptor we own.
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
    pub(crate) fn create_new(&self, name: &OsStr, mode: libc::mode_t) -> io::Result<File> {
        self.openat(name, libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL, mode).map(File::from)
    }

    pub(crate) fn mkdir(&self, name: &OsStr, mode: libc::mode_t) -> io::Result<()> {
        let c = cstr(name)?;
        // SAFETY: valid dirfd and NUL-terminated name.
        check(unsafe { libc::mkdirat(self.0.as_raw_fd(), c.as_ptr(), mode) }).map(|_| ())
    }

    /// Atomically rename `from` in this directory to `to` in `to_dir`.
    pub(crate) fn rename_to(&self, from: &OsStr, to_dir: &Dir, to: &OsStr) -> io::Result<()> {
        let (f, t) = (cstr(from)?, cstr(to)?);
        // SAFETY: valid dirfds and NUL-terminated names.
        check(unsafe { libc::renameat(self.0.as_raw_fd(), f.as_ptr(), to_dir.0.as_raw_fd(), t.as_ptr()) }).map(|_| ())
    }

    pub(crate) fn unlink(&self, name: &OsStr) -> io::Result<()> {
        let c = cstr(name)?;
        // SAFETY: valid dirfd and NUL-terminated name.
        check(unsafe { libc::unlinkat(self.0.as_raw_fd(), c.as_ptr(), 0) }).map(|_| ())
    }

    fn lstat(&self, name: &OsStr) -> io::Result<libc::stat> {
        let c = cstr(name)?;
        // SAFETY: `st` is fully written by a successful fstatat.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        check(unsafe { libc::fstatat(self.0.as_raw_fd(), c.as_ptr(), &mut st, libc::AT_SYMLINK_NOFOLLOW) })?;
        Ok(st)
    }

    /// `lstat` of an entry: (is regular file, is symlink).
    pub(crate) fn entry_kind(&self, name: &OsStr) -> io::Result<(bool, bool)> {
        let kind = self.lstat(name)?.st_mode & libc::S_IFMT;
        Ok((kind == libc::S_IFREG, kind == libc::S_IFLNK))
    }

    /// The stamp of an entry, without following a symlink.
    pub(crate) fn stamp(&self, name: &OsStr) -> io::Result<Stamp> {
        self.lstat(name).map(|st| Stamp::from_stat(&st))
    }

    /// Permission bits of this directory.
    pub(crate) fn mode(&self) -> io::Result<u32> {
        // SAFETY: `st` is fully written by a successful fstat.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        check(unsafe { libc::fstat(self.0.as_raw_fd(), &mut st) })?;
        Ok(st.st_mode as u32 & 0o7777)
    }

    /// Names of the entries of this directory (excluding `.` and `..`).
    pub(crate) fn entries(&self) -> io::Result<Vec<OsString>> {
        // SAFETY: dup returns a new descriptor that fdopendir takes ownership of.
        let dup = check(unsafe { libc::fcntl(self.0.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 0) })?;
        let stream = unsafe { libc::fdopendir(dup) };
        if stream.is_null() {
            let err = io::Error::last_os_error();
            unsafe { libc::close(dup) };
            return Err(err);
        }
        let mut names = Vec::new();
        loop {
            // SAFETY: `stream` is a valid DIR*; entries are copied before the next call.
            let entry = unsafe { libc::readdir(stream) };
            if entry.is_null() { break; }
            let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
            if name != b"." && name != b".." {
                names.push(OsString::from_vec(name.to_vec()));
            }
        }
        // SAFETY: closes the stream and the duplicated descriptor.
        unsafe { libc::closedir(stream) };
        Ok(names)
    }

    /// Take an exclusive advisory lock on this directory without waiting;
    /// it is released when the descriptor is closed (also on a crash).
    pub(crate) fn try_lock(&self) -> io::Result<()> {
        // SAFETY: valid descriptor; flock takes integer arguments only.
        check(unsafe { libc::flock(self.0.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) }).map(|_| ())
    }

    pub(crate) fn sync(&self) -> io::Result<()> {
        // SAFETY: valid descriptor.
        check(unsafe { libc::fsync(self.0.as_raw_fd()) }).map(|_| ())
    }
}
