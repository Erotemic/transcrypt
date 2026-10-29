//! Directory-handle relative filesystem operations for protected worktree
//! files: the Windows counterpart of `fsat.rs`, with the same interface.
//!
//! Every protected path is resolved once, component by component, with
//! `NtCreateFile` relative to the held parent directory handle
//! (`OBJECT_ATTRIBUTES.RootDirectory`), the Windows form of `openat`.
//! `FILE_OPEN_REPARSE_POINT` opens a symlink or junction itself instead of
//! following it, and such an entry is refused, as `O_NOFOLLOW` refuses a
//! symlink. Renames and deletions act on the file's own handle, relative
//! to the held target directory. A concurrent process that swaps a parent
//! directory for a junction after resolution cannot redirect a write.
//! Privacy is an owner-only DACL (`os_windows.rs`) where Unix uses modes.

use std::{
    cell::OnceCell,
    ffi::{OsStr, OsString},
    fs::File,
    io,
    mem::{offset_of, size_of, zeroed},
    os::windows::{ffi::{OsStrExt, OsStringExt}, fs::OpenOptionsExt, io::{AsRawHandle, FromRawHandle, OwnedHandle}},
    path::Path,
    ptr::{null, null_mut},
};
use windows_sys::{
    Wdk::{
        Foundation::OBJECT_ATTRIBUTES,
        Storage::FileSystem::{
            FileRenameInformation, FileRenameInformationEx, NtCreateFile, NtSetInformationFile, FILE_CREATE, FILE_DIRECTORY_FILE, FILE_NON_DIRECTORY_FILE, FILE_OPEN,
            FILE_OPEN_REPARSE_POINT, FILE_SYNCHRONOUS_IO_NONALERT,
        },
    },
    Win32::{
        Foundation::{RtlNtStatusToDosError, ERROR_NO_MORE_FILES, HANDLE, NTSTATUS, OBJ_CASE_INSENSITIVE, UNICODE_STRING},
        Security::SECURITY_DESCRIPTOR,
        Storage::FileSystem::{
            GetFileInformationByHandle, GetFileInformationByHandleEx, SetFileInformationByHandle,
            BY_HANDLE_FILE_INFORMATION, DELETE, FILE_ADD_FILE, FILE_ATTRIBUTE_DIRECTORY, FILE_ATTRIBUTE_NORMAL,
            FILE_ATTRIBUTE_REPARSE_POINT, FILE_DISPOSITION_FLAG_DELETE, FILE_DISPOSITION_FLAG_POSIX_SEMANTICS,
            FILE_DISPOSITION_INFO, FILE_DISPOSITION_INFO_EX, FILE_FLAG_BACKUP_SEMANTICS, FILE_FULL_DIR_INFO,
            FILE_GENERIC_READ, FILE_GENERIC_WRITE, FILE_LIST_DIRECTORY, FILE_READ_ATTRIBUTES, FILE_RENAME_INFO,
            FILE_SHARE_DELETE, FILE_SHARE_READ, FILE_SHARE_WRITE, FILE_TRAVERSE, FileDispositionInfo,
            FileDispositionInfoEx, FileFullDirectoryInfo, FileFullDirectoryRestartInfo, READ_CONTROL, SYNCHRONIZE,
            WRITE_DAC,
        },
        System::{IO::IO_STATUS_BLOCK, WindowsProgramming::{FILE_RENAME_FLAG_POSIX_SEMANTICS, FILE_RENAME_FLAG_REPLACE_IF_EXISTS}},
    },
};
use crate::os::{attribute_tag, privacy_problem, set_inherited, set_private, win32, PrivateDescriptor};

/// Bytes per UTF-16 code unit, the unit of NT name lengths.
const WCHAR: usize = size_of::<u16>();
/// UTF-16 code units of the characters a path component must not contain
/// (or, for `.` and space, end with).
const NUL: u16 = 0;
const SLASH: u16 = b'/' as u16;
const BACKSLASH: u16 = b'\\' as u16;
const COLON: u16 = b':' as u16;
const DOT: u16 = b'.' as u16;
const SPACE: u16 = b' ' as u16;
/// The size of the buffer a directory listing is read into, in aligned
/// 8-byte words.
const LISTING_BUFFER: usize = 64 * transcrypt_rs::KIB;
const WORD: usize = size_of::<u64>();
/// A Win32 `BOOLEAN` true (here `ReplaceIfExists`).
const BOOLEAN_TRUE: u32 = 1;

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.to_owned())
}

fn nt(status: NTSTATUS) -> io::Result<()> {
    if status >= 0 { return Ok(()); }
    // SAFETY: maps a status code to a Win32 error code.
    Err(io::Error::from_raw_os_error(unsafe { RtlNtStatusToDosError(status) } as i32))
}

/// Run `create` with the security descriptor of a new entry of `mode`:
/// owner-only (set atomically, never briefly open to others) when `mode`
/// has no group or other permissions; otherwise none, so it inherits.
fn with_mode<T>(mode: u32, create: impl FnOnce(*const SECURITY_DESCRIPTOR) -> io::Result<T>) -> io::Result<T> {
    let private = if mode & crate::modes::GROUP_OTHER_BITS == 0 { Some(PrivateDescriptor::new()?) } else { None };
    create(private.as_ref().map_or(null(), |d| d.as_ptr().cast_const().cast()))
}

/// One path component, in UTF-16, that names exactly the entry Git means:
/// no separator, no stream (`name:stream`), no NUL, and no trailing dot or
/// space (which Win32 path parsing, and so Git for Windows, would strip).
fn component(name: &OsStr) -> io::Result<Vec<u16>> {
    let wide: Vec<u16> = name.encode_wide().collect();
    let forbidden = |c: &u16| matches!(*c, NUL | SLASH | BACKSLASH | COLON);
    if wide.is_empty() || wide.iter().any(forbidden) || matches!(wide.last(), Some(&(DOT | SPACE))) {
        return Err(invalid("not a single path component"));
    }
    Ok(wide)
}

/// Identity, size and modification time of a file (as on Unix, not its
/// change time). Writing, truncating or replacing a file changes its stamp.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Stamp([i64; 4]);

fn information(handle: HANDLE) -> io::Result<BY_HANDLE_FILE_INFORMATION> {
    // SAFETY: plain data, for which all zeroes is a valid value.
    let mut info: BY_HANDLE_FILE_INFORMATION = unsafe { zeroed() };
    // SAFETY: a valid handle and out-pointer.
    win32(unsafe { GetFileInformationByHandle(handle, &mut info) })?;
    Ok(info)
}

impl Stamp {
    fn of_handle(handle: HANDLE) -> io::Result<Stamp> {
        let info = information(handle)?;
        let join = |high: u32, low: u32| ((high as i64) << u32::BITS) | low as i64;
        Ok(Stamp([
            info.dwVolumeSerialNumber as i64,
            join(info.nFileIndexHigh, info.nFileIndexLow),
            join(info.nFileSizeHigh, info.nFileSizeLow),
            join(info.ftLastWriteTime.dwHighDateTime, info.ftLastWriteTime.dwLowDateTime),
        ]))
    }

    /// The stamp of an open file.
    pub(crate) fn of(file: &File) -> io::Result<Stamp> {
        Stamp::of_handle(file.as_raw_handle())
    }
}

/// Permissions for a replacement file: whether it is private to this user.
/// Otherwise it gets the access its directory passes on.
#[derive(Clone, Copy)]
pub(crate) struct Mode(bool);

/// The replacement is written in the private staging directory, whose
/// owner-only access it inherits until `finish_replace`.
pub(crate) fn set_mode(_file: &File, _mode: Mode) -> io::Result<()> {
    Ok(())
}

/// The number of hard links to an open file.
pub(crate) fn links(file: &File) -> io::Result<u64> {
    Ok(information(file.as_raw_handle())?.nNumberOfLinks as u64)
}

/// An open directory, and the lock taken on it, if any.
pub(crate) struct Dir {
    handle: OwnedHandle,
    lock: OnceCell<OwnedHandle>,
}

impl Dir {
    /// Open a directory by path (the trusted repository root).
    pub(crate) fn open(path: &Path) -> io::Result<Dir> {
        let file = std::fs::OpenOptions::new().read(true).custom_flags(FILE_FLAG_BACKUP_SEMANTICS).open(path)?;
        if !file.metadata()?.is_dir() { return Err(invalid("not a directory")); }
        Ok(Dir { handle: file.into(), lock: OnceCell::new() })
    }

    fn raw(&self) -> HANDLE {
        self.handle.as_raw_handle()
    }

    /// `NtCreateFile` of `name` (UTF-16, possibly empty: this directory
    /// itself) relative to this directory, never following a reparse point.
    fn create(&self, name: &mut [u16], access: u32, share: u32, disposition: u32, options: u32,
        security: *const SECURITY_DESCRIPTOR) -> io::Result<OwnedHandle>
    {
        let bytes = u16::try_from(name.len() * WCHAR).map_err(|_| invalid("name too long"))?;
        let unicode = UNICODE_STRING { Length: bytes, MaximumLength: bytes, Buffer: name.as_mut_ptr() };
        let attributes = OBJECT_ATTRIBUTES {
            Length: size_of::<OBJECT_ATTRIBUTES>() as u32,
            RootDirectory: self.raw(),
            ObjectName: &unicode,
            // As Win32 (and so Git for Windows) names files.
            Attributes: OBJ_CASE_INSENSITIVE,
            SecurityDescriptor: security,
            SecurityQualityOfService: null(),
        };
        let mut handle: HANDLE = null_mut();
        // SAFETY: plain data, for which all zeroes is a valid value.
        let mut status: IO_STATUS_BLOCK = unsafe { zeroed() };
        // SAFETY: valid object attributes and out-pointers; the handle is owned.
        nt(unsafe {
            NtCreateFile(&mut handle, access | SYNCHRONIZE, &attributes, &mut status, null(), FILE_ATTRIBUTE_NORMAL,
                share, disposition, options | FILE_SYNCHRONOUS_IO_NONALERT | FILE_OPEN_REPARSE_POINT, null(), 0)
        })?;
        // SAFETY: a fresh handle we own.
        Ok(unsafe { OwnedHandle::from_raw_handle(handle) })
    }

    /// Open the entry `name` itself, whatever it is.
    fn entry(&self, name: &OsStr, access: u32, disposition: u32, options: u32,
        security: *const SECURITY_DESCRIPTOR) -> io::Result<OwnedHandle>
    {
        let share = FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE;
        self.create(&mut component(name)?, access, share, disposition, options, security)
    }

    /// Open `name`, refusing a symlink, junction or other reparse point.
    fn openat(&self, name: &OsStr, access: u32, disposition: u32, options: u32,
        security: *const SECURITY_DESCRIPTOR) -> io::Result<OwnedHandle>
    {
        let handle = self.entry(name, access | FILE_READ_ATTRIBUTES, disposition, options, security)?;
        if attribute_tag(handle.as_raw_handle())?.0 & FILE_ATTRIBUTE_REPARSE_POINT != 0 {
            return Err(invalid("a symlink, junction or other reparse point"));
        }
        Ok(handle)
    }

    /// Open the regular file `name` to change its DACL, refusing a reparse point.
    fn open_dac(&self, name: &OsStr) -> io::Result<OwnedHandle> {
        self.openat(name, WRITE_DAC | READ_CONTROL, FILE_OPEN, FILE_NON_DIRECTORY_FILE, null())
    }

    /// A subdirectory; fails if `name` is a reparse point or not a directory.
    pub(crate) fn subdir(&self, name: &OsStr) -> io::Result<Dir> {
        let access = FILE_LIST_DIRECTORY | FILE_TRAVERSE | READ_CONTROL;
        let handle = self.openat(name, access, FILE_OPEN, FILE_DIRECTORY_FILE, null())?;
        Ok(Dir { handle, lock: OnceCell::new() })
    }

    /// Open `name` for reading; fails on reparse points and non-regular files.
    pub(crate) fn open_regular(&self, name: &OsStr) -> io::Result<File> {
        let file = File::from(self.openat(name, FILE_GENERIC_READ, FILE_OPEN, FILE_NON_DIRECTORY_FILE, null())?);
        if !file.metadata()?.is_file() { return Err(invalid("not a regular file")); }
        Ok(file)
    }

    /// Exclusively create a new regular file; `mode` without group or
    /// other permissions makes it owner-only, otherwise it inherits.
    pub(crate) fn create_new(&self, name: &OsStr, mode: u32) -> io::Result<File> {
        let access = FILE_GENERIC_WRITE | FILE_GENERIC_READ | DELETE;
        with_mode(mode, |security| self.openat(name, access, FILE_CREATE, FILE_NON_DIRECTORY_FILE, security)).map(File::from)
    }

    /// Create a directory; one that already exists (whatever it is) is not
    /// an error: open it with `subdir`, which refuses anything else. A mode
    /// without group or other permissions makes it owner-only.
    pub(crate) fn mkdir(&self, name: &OsStr, mode: u32) -> io::Result<()> {
        match with_mode(mode, |security| self.entry(name, FILE_LIST_DIRECTORY, FILE_CREATE, FILE_DIRECTORY_FILE, security)) {
            Err(e) if e.kind() != io::ErrorKind::AlreadyExists => Err(e),
            _ => Ok(()),
        }
    }

    /// Atomically rename `from` in this directory to `to` in `to_dir`,
    /// replacing what is there (with POSIX semantics where the file system
    /// has them: also when another program has the old file open). Through
    /// ntdll: kernel32's `SetFileInformationByHandle` refuses a rename
    /// relative to a directory handle.
    pub(crate) fn rename_to(&self, from: &OsStr, to_dir: &Dir, to: &OsStr) -> io::Result<()> {
        let source = self.entry(from, DELETE, FILE_OPEN, 0, null())?;
        let target = component(to)?;
        let offset = offset_of!(FILE_RENAME_INFO, FileName);
        let size = offset + target.len() * WCHAR;
        // Room for a terminating NUL, in aligned words.
        let mut buffer = vec![0u64; (size + WCHAR).div_ceil(WORD)];
        let mut rename = |class, flags: u32| {
            // FILE_RENAME_INFORMATION has FILE_RENAME_INFO's layout.
            let info = buffer.as_mut_ptr().cast::<FILE_RENAME_INFO>();
            // SAFETY: plain data, for which all zeroes is a valid value.
            let mut status: IO_STATUS_BLOCK = unsafe { zeroed() };
            // SAFETY: the buffer is aligned and holds the header and the name.
            unsafe {
                (*info).Anonymous.Flags = flags;
                (*info).RootDirectory = to_dir.raw();
                (*info).FileNameLength = (target.len() * WCHAR) as u32;
                std::ptr::copy_nonoverlapping(target.as_ptr(), buffer.as_mut_ptr().cast::<u8>().add(offset).cast(), target.len());
                nt(NtSetInformationFile(source.as_raw_handle(), &mut status, buffer.as_ptr().cast(), size as u32, class))
            }
        };
        rename(FileRenameInformationEx, FILE_RENAME_FLAG_REPLACE_IF_EXISTS | FILE_RENAME_FLAG_POSIX_SEMANTICS)
            // `ReplaceIfExists` (a BOOLEAN in the same place) where the
            // extended rename is unsupported (older Windows, FAT).
            .or_else(|_| rename(FileRenameInformation, BOOLEAN_TRUE))
    }

    pub(crate) fn unlink(&self, name: &OsStr) -> io::Result<()> {
        let file = self.entry(name, DELETE, FILE_OPEN, FILE_NON_DIRECTORY_FILE, null())?;
        let posix = FILE_DISPOSITION_INFO_EX { Flags: FILE_DISPOSITION_FLAG_DELETE | FILE_DISPOSITION_FLAG_POSIX_SEMANTICS };
        // SAFETY: a valid handle and information buffers of their classes.
        win32(unsafe {
            SetFileInformationByHandle(file.as_raw_handle(), FileDispositionInfoEx, (&posix as *const FILE_DISPOSITION_INFO_EX).cast(),
                size_of::<FILE_DISPOSITION_INFO_EX>() as u32)
        }).or_else(|_| {
            let delete = FILE_DISPOSITION_INFO { DeleteFile: true };
            // SAFETY: as above.
            win32(unsafe {
                SetFileInformationByHandle(file.as_raw_handle(), FileDispositionInfo, (&delete as *const FILE_DISPOSITION_INFO).cast(),
                    size_of::<FILE_DISPOSITION_INFO>() as u32)
            })
        })
    }

    /// The entry itself: (is regular file, is symlink or other reparse point).
    pub(crate) fn entry_kind(&self, name: &OsStr) -> io::Result<(bool, bool)> {
        let handle = self.entry(name, FILE_READ_ATTRIBUTES, FILE_OPEN, 0, null())?;
        let (attributes, _) = attribute_tag(handle.as_raw_handle())?;
        let link = attributes & FILE_ATTRIBUTE_REPARSE_POINT != 0;
        Ok((!link && attributes & FILE_ATTRIBUTE_DIRECTORY == 0, link))
    }

    /// The stamp of an entry, without following a reparse point.
    pub(crate) fn stamp(&self, name: &OsStr) -> io::Result<Stamp> {
        Stamp::of_handle(self.entry(name, FILE_READ_ATTRIBUTES, FILE_OPEN, 0, null())?.as_raw_handle())
    }

    /// The permissions for a file replacing the entry `name`.
    pub(crate) fn replacement_mode(&self, name: &OsStr, private: bool) -> io::Result<Mode> {
        self.entry(name, FILE_READ_ATTRIBUTES, FILE_OPEN, 0, null())?;
        Ok(Mode(private))
    }

    /// After `name` was renamed into this directory from the private
    /// staging directory: give it the access its directory passes on, or
    /// keep it owner-only (there is nothing to sync: see `sync`).
    pub(crate) fn finish_replace(&self, name: &OsStr, mode: Mode) -> io::Result<()> {
        let file = self.open_dac(name)?;
        if mode.0 { set_private(file.as_raw_handle()) } else { set_inherited(file.as_raw_handle()) }
    }

    /// Restrict the regular file `name` to this user (never following a
    /// reparse point).
    pub(crate) fn make_private(&self, name: &OsStr) -> io::Result<()> {
        set_private(self.open_dac(name)?.as_raw_handle())
    }

    /// Why others than this user, its owner, can enter this directory, if
    /// they can.
    pub(crate) fn privacy_problem(&self) -> io::Result<Option<String>> {
        privacy_problem(self.raw())
    }

    /// Names of the entries of this directory (excluding `.` and `..`).
    pub(crate) fn entries(&self) -> io::Result<Vec<OsString>> {
        let mut names = Vec::new();
        let mut buffer = vec![0u64; LISTING_BUFFER / WORD];
        let mut class = FileFullDirectoryRestartInfo;
        loop {
            // SAFETY: a directory handle and a buffer of the given size.
            let ok = unsafe { GetFileInformationByHandleEx(self.raw(), class, buffer.as_mut_ptr().cast(), (buffer.len() * WORD) as u32) };
            if ok == 0 {
                let error = io::Error::last_os_error();
                if error.raw_os_error() == Some(ERROR_NO_MORE_FILES as i32) { return Ok(names); }
                return Err(error);
            }
            class = FileFullDirectoryInfo;
            let base = buffer.as_ptr().cast::<u8>();
            let mut offset = 0usize;
            loop {
                // SAFETY: Windows filled the buffer with a chain of entries,
                // each at an aligned offset given by the one before.
                let entry = unsafe { &*base.add(offset).cast::<FILE_FULL_DIR_INFO>() };
                let name = unsafe {
                    std::slice::from_raw_parts(base.add(offset + offset_of!(FILE_FULL_DIR_INFO, FileName)).cast::<u16>(),
                        entry.FileNameLength as usize / WCHAR)
                };
                if name != [DOT] && name != [DOT, DOT] { names.push(OsString::from_wide(name)); }
                if entry.NextEntryOffset == 0 { break; }
                offset += entry.NextEntryOffset as usize;
            }
        }
    }

    /// Take an exclusive lock on this directory without waiting; it is
    /// released when the directory is closed (also on a crash). It is a
    /// second handle to this directory that asks to add files and lets no
    /// other handle ask the same, so a second lock fails with a sharing
    /// violation, while ordinary access to the directory is unaffected.
    pub(crate) fn try_lock(&self) -> io::Result<()> {
        if self.lock.get().is_some() { return Ok(()); }
        let lock = self.create(&mut [], FILE_ADD_FILE, FILE_SHARE_READ | FILE_SHARE_DELETE, FILE_OPEN, FILE_DIRECTORY_FILE, null())?;
        let _ = self.lock.set(lock);
        Ok(())
    }

    /// Windows has no directory fsync for unprivileged handles; NTFS
    /// journals the directory change.
    pub(crate) fn sync(&self) -> io::Result<()> {
        Ok(())
    }
}
