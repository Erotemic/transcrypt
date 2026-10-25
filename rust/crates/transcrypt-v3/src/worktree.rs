//! Protected worktree files resolved race-free (dirfd-relative, no
//! symlinks) and the private, locked staging directory for replacements.

use std::{
    ffi::{OsStr, OsString},
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
};
use std::os::unix::ffi::OsStringExt;
use zeroize::Zeroizing;
use crate::{fsat, git::read_limited};
use transcrypt_v3_core::MAX_RECORD;

pub(crate) fn indexed_path(path: &[u8]) -> Result<PathBuf, String> {
    #[cfg(unix)]
    let relative = PathBuf::from(std::ffi::OsString::from_vec(path.to_vec()));
    #[cfg(not(unix))]
    let relative = PathBuf::from(String::from_utf8(path.to_vec()).map_err(|_| "non-UTF8 path unsupported")?);
    if relative.is_absolute() || relative.components().any(|c| matches!(c, std::path::Component::ParentDir | std::path::Component::RootDir)) {
        return Err("unsafe protected relative path".into());
    }
    Ok(relative)
}

/// A protected worktree file resolved race-free: its parent directory is
/// held open, every component having been opened with `O_NOFOLLOW`.
pub(crate) struct Protected {
    dir: fsat::Dir,
    leaf: OsString,
}

/// Resolve a Git-relative path below the repository root, refusing symlinks
/// and non-directories in *every* component and a non-regular leaf.
pub(crate) fn open_protected(root: &Path, relative: &Path) -> Result<Protected, String> {
    find_protected(root, relative)?.ok_or_else(|| "protected worktree path missing".into())
}

/// Like `open_protected`, but `None` when the file (or a parent directory)
/// does not exist: a deleted or sparse-checkout file holds no plaintext.
pub(crate) fn find_protected(root: &Path, relative: &Path) -> Result<Option<Protected>, String> {
    let parts: Vec<_> = relative.components().collect();
    let Some((leaf, parents)) = parts.split_last() else {
        return Err("empty protected worktree path".into());
    };
    let mut dir = fsat::Dir::open(root).map_err(|_| "cannot open repository root")?;
    for part in parents {
        let std::path::Component::Normal(name) = part else {
            return Err("unsafe protected path component".into());
        };
        dir = match dir.subdir(name) {
            Ok(dir) => dir,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(_) => return Err("protected worktree parent is a symlink or not a directory".into()),
        };
    }
    let std::path::Component::Normal(leaf) = leaf else {
        return Err("unsafe protected path component".into());
    };
    let (regular, link) = match dir.entry_kind(leaf) {
        Ok(kind) => kind,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(_) => return Err("cannot examine protected worktree path".into()),
    };
    if link { return Err("symlink in protected path rejected".into()); }
    if !regular { return Err("protected worktree entry is not a regular file".into()); }
    Ok(Some(Protected { dir, leaf: leaf.to_os_string() }))
}

impl Protected {
    /// Remove group and other permissions (through an `O_NOFOLLOW`
    /// descriptor, so a swapped-in symlink is never followed).
    pub(crate) fn make_private(&self) -> Result<(), String> {
        use std::os::unix::fs::PermissionsExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        let mode = file.metadata().map_err(|_| "cannot stat protected worktree file")?.permissions().mode();
        if mode & 0o077 != 0 {
            file.set_permissions(fs::Permissions::from_mode(mode & 0o700))
                .map_err(|_| "cannot restrict protected worktree file permissions")?;
        }
        Ok(())
    }

    /// Number of hard links to the file.
    pub(crate) fn links(&self) -> Result<u64, String> {
        use std::os::unix::fs::MetadataExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        Ok(file.metadata().map_err(|_| "cannot stat protected worktree file")?.nlink())
    }

    /// Whether group or other users may read the file.
    pub(crate) fn readable_by_others(&self) -> Result<bool, String> {
        use std::os::unix::fs::PermissionsExt;
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        let mode = file.metadata().map_err(|_| "cannot stat protected worktree file")?.permissions().mode();
        Ok(mode & 0o044 != 0)
    }

    /// The contents and the stamp of the file they were read from.
    pub(crate) fn read(&self) -> Result<(Zeroizing<Vec<u8>>, fsat::Stamp), String> {
        let file = self.dir.open_regular(&self.leaf)
            .map_err(|_| "cannot read protected worktree file (missing, symlink or not regular)")?;
        let stamp = fsat::Stamp::of(&file).map_err(|_| "cannot stat protected worktree file")?;
        let contents = Zeroizing::new(read_limited(&file, MAX_RECORD)?);
        if fsat::Stamp::of(&file).map_err(|_| "cannot stat protected worktree file")? != stamp {
            return Err("protected worktree file changed while it was read".into());
        }
        Ok((contents, stamp))
    }

    /// Replace the file by `contents` through an exclusive mode-0600 file in
    /// the private staging directory, fsync, `renameat` into the held parent
    /// directory, then fsync that directory. The entry must still have the
    /// `expected` stamp of the read that justified the replacement, so an
    /// edit made since then is refused instead of being lost (a same-UID
    /// writer can still race the final check and the rename). A
    /// cross-filesystem rename fails closed (EXDEV) without touching the
    /// file. Not a multi-file transaction.
    pub(crate) fn replace(&self, staging: &Staging, contents: &[u8], slot: usize, expected: &fsat::Stamp) -> Result<(), String> {
        let temp = OsString::from(format!("{}-{slot}.tmp", std::process::id()));
        let mut file = staging.dir.create_new(&temp, 0o600)
            .map_err(|e| format!("cannot create private staged file: {e}"))?;
        let result = file.write_all(contents).and_then(|_| file.sync_all());
        drop(file);
        if let Err(e) = result {
            let _ = staging.dir.unlink(&temp);
            return Err(format!("cannot write private staged file: {e}"));
        }
        if self.dir.stamp(&self.leaf).ok().as_ref() != Some(expected) {
            let _ = staging.dir.unlink(&temp);
            return Err("protected worktree file changed after it was checked; refusing to replace it".into());
        }
        if let Err(e) = staging.dir.rename_to(&temp, &self.dir, &self.leaf) {
            let _ = staging.dir.unlink(&temp);
            return Err(format!("cannot replace protected worktree file: {e}"));
        }
        self.dir.sync().map_err(|e| format!("cannot sync protected file directory: {e}"))
    }
}

/// Private staging directory for whole-file replacements:
/// `.git/transcrypt-v3-staging`, a real mode-0700 directory held open by fd.
/// Temporaries never live in the worktree, so a crash cannot leave plaintext
/// where `git add` could commit it unencrypted, and Git never reads files
/// under `.git`. Holding it also holds an exclusive lock, so worktree-
/// mutating operations (`hydrate`, `lock`) never interleave, and anything
/// left in it is from an interrupted earlier run and is removed.
pub(crate) struct Staging {
    dir: fsat::Dir,
}

pub(crate) fn staging_dir(root: &Path) -> Result<Staging, String> {
    let git_dir = fsat::Dir::open(&crate::git::git_dir(root)).map_err(|_| "cannot open the Git directory")?;
    let name = OsStr::new("transcrypt-v3-staging");
    match git_dir.mkdir(name, 0o700) {
        Ok(()) => {},
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {},
        Err(e) => return Err(format!("cannot create private staging directory: {e}")),
    }
    let dir = git_dir.subdir(name)
        .map_err(|_| "unsafe .git/transcrypt-v3-staging; require a real 0700 directory")?;
    if dir.mode().map_err(|_| "cannot examine private staging directory")? & 0o077 != 0 {
        return Err("unsafe .git/transcrypt-v3-staging; require a real 0700 directory".into());
    }
    dir.try_lock().map_err(|_| "another transcrypt-v3 hydrate or lock is running in this repository")?;
    for entry in dir.entries().map_err(|_| "cannot list private staging directory")? {
        let (regular, _) = dir.entry_kind(&entry).map_err(|_| "cannot examine stale staged file")?;
        if !regular {
            return Err("unexpected entry in private staging directory".into());
        }
        dir.unlink(&entry).map_err(|e| format!("cannot remove stale staged file: {e}"))?;
    }
    Ok(Staging { dir })
}

/// `.git/transcrypt-v3-scratch`: a real mode-0700 directory for plaintext
/// that another program must read as a file (the merge and diff drivers'
/// inputs). Files are exclusive and mode 0600, named after this process, and
/// removed when the `Scratch` is dropped. Files of processes that no longer
/// run (a crash) are removed on the next use. No secure-erasure claim.
pub(crate) struct Scratch {
    dir: fsat::Dir,
    path: PathBuf,
    prefix: String,
    written: std::cell::RefCell<Vec<OsString>>,
}

impl Scratch {
    const NAME: &'static str = "transcrypt-v3-scratch";

    pub(crate) fn create(root: &Path) -> Result<Scratch, String> {
        let path = crate::git::git_dir(root).join(Self::NAME);
        let git_dir = fsat::Dir::open(&crate::git::git_dir(root)).map_err(|_| "cannot open the Git directory")?;
        let name = OsStr::new(Self::NAME);
        match git_dir.mkdir(name, 0o700) {
            Ok(()) => {},
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {},
            Err(e) => return Err(format!("cannot create private scratch directory: {e}")),
        }
        let dir = git_dir.subdir(name).map_err(|_| "unsafe .git/transcrypt-v3-scratch")?;
        if dir.mode().map_err(|_| "cannot examine private scratch directory")? & 0o077 != 0 {
            return Err("unsafe .git/transcrypt-v3-scratch; require a real 0700 directory".into());
        }
        for entry in dir.entries().map_err(|_| "cannot list private scratch directory")? {
            let owner = entry.to_str().and_then(|n| n.split('-').next()).and_then(|p| p.parse::<i32>().ok());
            // SAFETY: kill with signal 0 only checks whether the process exists.
            let running = owner.is_some_and(|pid| unsafe { libc::kill(pid, 0) } == 0
                || io::Error::last_os_error().raw_os_error() == Some(libc::EPERM));
            if !running {
                let _ = dir.unlink(&entry);
            }
        }
        Ok(Scratch { dir, path, prefix: std::process::id().to_string(), written: Default::default() })
    }

    /// Write `contents` to a new private file; returns its absolute path.
    pub(crate) fn write(&self, name: &str, contents: &[u8]) -> Result<PathBuf, String> {
        let file_name = OsString::from(format!("{}-{name}", self.prefix));
        let mut file = self.dir.create_new(&file_name, 0o600)
            .map_err(|e| format!("cannot create private scratch file: {e}"))?;
        self.written.borrow_mut().push(file_name.clone());
        file.write_all(contents).map_err(|e| format!("cannot write private scratch file: {e}"))?;
        Ok(self.path.join(file_name))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        for name in self.written.borrow().iter() {
            let _ = self.dir.unlink(name);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn replacement_is_private_and_leaves_no_worktree_temporaries() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = std::env::temp_dir().join(format!(
            "transcrypt-v3-replace-{}", std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(tmp.join(".git")).unwrap();
        let sdir = tmp.join(".git/transcrypt-v3-staging");
        drop(staging_dir(&tmp).unwrap());
        assert_eq!(fs::metadata(&sdir).unwrap().permissions().mode() & 0o777, 0o700);
        // A crash-leftover temporary is purged on the next use.
        fs::write(sdir.join("stale.tmp"), b"stale plaintext").unwrap();
        let staging = staging_dir(&tmp).unwrap();
        // A concurrent operation cannot enter (or purge) while it is held.
        assert!(staging_dir(&tmp).is_err());
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        let path = tmp.join("item.secret");
        fs::write(&path, b"ciphertext placeholder").unwrap();
        let target = open_protected(&tmp, Path::new("item.secret")).unwrap();
        let (_, stamp) = target.read().unwrap();
        target.replace(&staging, b"authenticated plaintext", 0, &stamp).unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"authenticated plaintext");
        assert_eq!(fs::metadata(&path).unwrap().permissions().mode() & 0o077, 0);
        assert_eq!(fs::read_dir(&tmp).unwrap().count(), 2, "only .git and the file");
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        // A symlinked or loosely permissioned staging directory is refused.
        fs::remove_dir(&sdir).unwrap();
        std::os::unix::fs::symlink(&tmp, &sdir).unwrap();
        assert!(staging_dir(&tmp).is_err());
        fs::remove_file(&sdir).unwrap();
        fs::create_dir(&sdir).unwrap();
        fs::set_permissions(&sdir, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(staging_dir(&tmp).is_err());
        fs::remove_dir_all(&tmp).unwrap();
    }

    /// Randomized robustness of the adapter's parsers of Git output: no
    /// input panics, every accepted record round-trips to exactly what Git
    /// would print for it, and mutations of valid input are either rejected
    /// or still exact.
    #[test]
    fn replacement_refuses_a_file_changed_since_it_was_checked() {
        let tmp = std::env::temp_dir().join(format!(
            "transcrypt-v3-stamp-{}", std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(tmp.join(".git")).unwrap();
        let staging = staging_dir(&tmp).unwrap();
        let path = tmp.join("item.secret");
        fs::write(&path, b"checked contents").unwrap();
        let target = open_protected(&tmp, Path::new("item.secret")).unwrap();
        let (_, stamp) = target.read().unwrap();
        // A concurrent edit after the check, even one of the same size.
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(&path, b"edited contents!").unwrap();
        assert!(target.replace(&staging, b"replacement", 0, &stamp).is_err());
        assert_eq!(fs::read(&path).unwrap(), b"edited contents!", "edit must survive");
        // So is a file replaced by a different inode.
        let (_, stamp) = target.read().unwrap();
        fs::remove_file(&path).unwrap();
        fs::write(&path, b"edited contents!").unwrap();
        assert!(target.replace(&staging, b"replacement", 1, &stamp).is_err());
        assert_eq!(fs::read_dir(tmp.join(".git/transcrypt-v3-staging")).unwrap().count(), 0);
        fs::remove_dir_all(&tmp).unwrap();
    }

    #[test]
    fn protected_parent_symlinks_cannot_redirect_lock_or_hydrate() {
        use std::os::unix::fs::symlink;
        let tmp = std::env::temp_dir().join(format!(
            "transcrypt-v3-parent-symlink-{}", std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir(&tmp).unwrap();
        let external = tmp.join("external");
        fs::create_dir(&external).unwrap();
        fs::write(external.join("item.secret"), b"test").unwrap();
        let checkout = tmp.join("checkout");
        fs::create_dir_all(checkout.join(".git")).unwrap();
        symlink(&external, checkout.join("linked")).unwrap();
        assert!(open_protected(&checkout, Path::new("linked/item.secret")).is_err());
        symlink(external.join("item.secret"), checkout.join("leaf.secret")).unwrap();
        assert!(open_protected(&checkout, Path::new("leaf.secret")).is_err());
        fs::create_dir(checkout.join("regular")).unwrap();
        fs::write(checkout.join("regular/item.secret"), b"test").unwrap();
        let target = open_protected(&checkout, Path::new("regular/item.secret")).unwrap();
        let (contents, stamp) = target.read().unwrap();
        assert_eq!(*contents, b"test");
        // Race: after resolution, the parent is swapped for a symlink to an
        // outside directory. The held directory fd keeps the write inside.
        let staging = staging_dir(&checkout).unwrap();
        fs::rename(checkout.join("regular"), checkout.join("moved")).unwrap();
        symlink(&external, checkout.join("regular")).unwrap();
        target.replace(&staging, b"plaintext", 0, &stamp).unwrap();
        assert_eq!(fs::read(external.join("item.secret")).unwrap(), b"test", "write escaped");
        assert_eq!(fs::read(checkout.join("moved/item.secret")).unwrap(), b"plaintext");
        let _ = fs::remove_dir_all(tmp);
    }
}
