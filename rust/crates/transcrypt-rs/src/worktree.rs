//! Protected worktree files resolved race-free (relative to held directory
//! descriptors or handles, never through a symlink or reparse point) and the
//! private, locked staging directory for replacements.

use std::{
    ffi::{OsStr, OsString},
    io::{self, Write},
    path::{Component, Path, PathBuf},
};
use zeroize::Zeroizing;
use crate::{fsat, git::read_record, modes};

/// A Git path as a relative OS path. Only a root and `..` are refused here:
/// a Windows prefix (`C:`) or a leading `.` is not a plain name, which
/// `names` refuses when the path is opened.
pub(crate) fn indexed_path(path: &[u8]) -> Result<PathBuf, String> {
    let relative = PathBuf::from(crate::os::os_string(path)?);
    if relative.is_absolute() || relative.components().any(|c| matches!(c, Component::ParentDir | Component::RootDir)) {
        return Err("unsafe protected relative path".into());
    }
    Ok(relative)
}

/// The components of `relative`, parents first, if every one is a plain
/// name (no root, prefix, `.` or `..`) to open in its parent.
fn names(relative: &Path) -> Option<Vec<&OsStr>> {
    relative.components().map(|c| match c { Component::Normal(name) => Some(name), _ => None }).collect()
}

/// A protected worktree file resolved race-free: its parent directory is
/// held open, no component having been opened through a symlink or
/// reparse point.
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
    let names = names(relative).ok_or("unsafe protected path component")?;
    let Some((leaf, parents)) = names.split_last() else {
        return Err("empty protected worktree path".into());
    };
    let mut dir = fsat::Dir::open(root).map_err(|_| "cannot open repository root")?;
    for name in parents {
        dir = match dir.subdir(name) {
            Ok(dir) => dir,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(_) => return Err("protected worktree parent is a symlink or not a directory".into()),
        };
    }
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
    /// Make the file owner-only (never following a swapped-in symlink or
    /// reparse point). Private mode.
    pub(crate) fn make_private(&self) -> Result<(), String> {
        self.dir.make_private(&self.leaf).map_err(|_| "cannot restrict protected worktree file permissions".into())
    }

    /// Number of hard links to the file.
    pub(crate) fn links(&self) -> Result<u64, String> {
        let file = self.dir.open_regular(&self.leaf).map_err(|_| "cannot open protected worktree file")?;
        fsat::links(&file).map_err(|_| "cannot stat protected worktree file".into())
    }

    /// The contents and the stamp of the file they were read from.
    pub(crate) fn read(&self) -> Result<(Zeroizing<Vec<u8>>, fsat::Stamp), String> {
        let file = self.dir.open_regular(&self.leaf)
            .map_err(|_| "cannot read protected worktree file (missing, symlink or not regular)")?;
        let stamp = fsat::Stamp::of(&file).map_err(|_| "cannot stat protected worktree file")?;
        let contents = read_record(&file)?;
        if fsat::Stamp::of(&file).map_err(|_| "cannot stat protected worktree file")? != stamp {
            return Err("protected worktree file changed while it was read".into());
        }
        Ok((contents, stamp))
    }

    /// Replace the file by `contents` through an exclusive owner-only file
    /// in the private staging directory, synced, then renamed into the held
    /// parent directory, which is synced too (Windows journals the rename).
    /// The new file keeps the old one's permissions (an executable stays
    /// executable; on Windows, the access its directory gives), restricted
    /// to this user when `private`. The entry must still have the `expected`
    /// stamp of the read that justified the replacement, so an edit made
    /// since then is refused instead of being lost (a same-UID writer can
    /// still race the final check and the rename). A cross-filesystem
    /// rename fails closed without touching the file. Not a multi-file
    /// transaction.
    pub(crate) fn replace(&self, staging: &Staging, contents: &[u8], expected: &fsat::Stamp, private: bool) -> Result<(), String> {
        let mode = self.dir.replacement_mode(&self.leaf, private).map_err(|_| "cannot stat protected worktree file")?;
        let temp = staging.temporary();
        let mut file = staging.dir.create_new(&temp, modes::PRIVATE_FILE)
            .map_err(|e| format!("cannot create private staged file: {e}"))?;
        // Until the rename, a failure removes the temporary.
        let fail = |message: String| -> Result<(), String> {
            let _ = staging.dir.unlink(&temp);
            Err(message)
        };
        let result = file.write_all(contents)
            .and_then(|_| fsat::set_mode(&file, mode))
            .and_then(|_| file.sync_all());
        drop(file);
        if let Err(e) = result {
            return fail(format!("cannot write private staged file: {e}"));
        }
        if self.dir.stamp(&self.leaf).ok().as_ref() != Some(expected) {
            return fail("protected worktree file changed after it was checked; refusing to replace it".into());
        }
        if let Err(e) = staging.dir.rename_to(&temp, &self.dir, &self.leaf) {
            return fail(format!("cannot replace protected worktree file: {e}"));
        }
        self.dir.finish_replace(&self.leaf, mode).map_err(|e| format!("cannot sync protected file directory: {e}"))
    }
}

/// Replace the worktree file of `path` by `contents` if it still holds
/// exactly `expected` (a missing file is left alone).
pub(crate) fn replace_if_holds(root: &Path, staging: &Staging, path: &[u8], expected: &[u8], contents: &[u8], private: bool)
    -> Result<(), String>
{
    if let Some(target) = find_protected(root, &indexed_path(path)?)? {
        let (worktree, stamp) = target.read()?;
        if *worktree == *expected { target.replace(staging, contents, &stamp, private)?; }
    }
    Ok(())
}

/// Write a repository file that v3 maintains (`.gitattributes`,
/// `.transcrypt/config`): replace it if it exists, else create it, with the
/// same symlink- and reparse-point-refusing resolution and staged atomic
/// rename as protected files. A committed symlink at the path or in a
/// parent is refused, never followed, so the write cannot land outside the
/// repository.
pub(crate) fn write_repository_file(root: &Path, staging: &Staging, relative: &Path, contents: &[u8]) -> Result<(), String> {
    if let Some(target) = find_protected(root, relative)? {
        let (_, stamp) = target.read()?;
        return target.replace(staging, contents, &stamp, false);
    }
    let names = names(relative).unwrap_or_default();
    let Some((leaf, parents)) = names.split_last() else {
        return Err("unsafe repository file path".into());
    };
    let mut dir = fsat::Dir::open(root).map_err(|_| "cannot open repository root")?;
    for name in parents {
        dir.mkdir(name, modes::NEW_DIR).map_err(|e| format!("cannot create {}: {e}", relative.display()))?;
        dir = dir.subdir(name).map_err(|_| format!("{} has a parent that is a symlink or not a directory", relative.display()))?;
    }
    let mut file = dir.create_new(leaf, modes::NEW_FILE).map_err(|e| format!("cannot create {}: {e}", relative.display()))?;
    file.write_all(contents).and_then(|_| file.sync_all())
        .map_err(|e| format!("cannot write {}: {e}", relative.display()))?;
    dir.sync().map_err(|e| format!("cannot sync {}: {e}", relative.display()))
}

/// Private staging directory for whole-file replacements:
/// `.git/transcrypt-v3-staging`, a real owner-only directory (not a symlink
/// or reparse point), held open.
/// Temporaries never live in the worktree, so a crash cannot leave plaintext
/// where `git add` could commit it unencrypted, and Git never reads files
/// under `.git`. Holding it also holds an exclusive lock, so worktree-
/// mutating operations (`hydrate`, `lock`) never interleave, and anything
/// left in it is from an interrupted earlier run and is removed.
pub(crate) struct Staging {
    dir: fsat::Dir,
    next: std::cell::Cell<usize>,
}

impl Staging {
    /// A fresh name for a temporary in this (locked, private) directory.
    fn temporary(&self) -> OsString {
        let slot = self.next.get();
        self.next.set(slot + 1);
        OsString::from(format!("{}-{slot}.tmp", std::process::id()))
    }
}

/// `.git/<name>`, created if missing: a real directory (not a symlink)
/// that only this user can enter. `what` names it in errors.
fn private_git_dir(root: &Path, name: &str, what: &str) -> Result<fsat::Dir, String> {
    let git_dir = fsat::Dir::open(&crate::git::git_dir(root)).map_err(|_| "cannot open the Git directory")?;
    let unsafe_dir = |why: &str| format!("unsafe .git/{name}: {why}; require a real {:04o} directory", modes::PRIVATE_DIR);
    git_dir.mkdir(OsStr::new(name), modes::PRIVATE_DIR).map_err(|e| format!("cannot create private {what} directory: {e}"))?;
    let dir = git_dir.subdir(OsStr::new(name)).map_err(|_| unsafe_dir("it is not a real directory"))?;
    if let Some(why) = dir.privacy_problem().map_err(|_| format!("cannot examine private {what} directory"))? {
        return Err(unsafe_dir(&why));
    }
    Ok(dir)
}

pub(crate) fn staging_dir(root: &Path) -> Result<Staging, String> {
    let dir = private_git_dir(root, "transcrypt-v3-staging", "staging")?;
    dir.try_lock().map_err(|_| "another transcrypt-rs hydrate or lock is running in this repository")?;
    for entry in dir.entries().map_err(|_| "cannot list private staging directory")? {
        let (regular, _) = dir.entry_kind(&entry).map_err(|_| "cannot examine stale staged file")?;
        if !regular {
            return Err("unexpected entry in private staging directory".into());
        }
        dir.unlink(&entry).map_err(|e| format!("cannot remove stale staged file: {e}"))?;
    }
    Ok(Staging { dir, next: std::cell::Cell::new(0) })
}

/// `.git/transcrypt-v3-scratch`: a real owner-only directory for plaintext
/// that another program must read as a file (the merge and diff drivers'
/// inputs). Files are exclusive and owner-only, named after this process, and
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
        let dir = private_git_dir(root, Self::NAME, "scratch")?;
        for entry in dir.entries().map_err(|_| "cannot list private scratch directory")? {
            let owner = entry.to_str().and_then(|n| n.split('-').next()).and_then(|p| p.parse::<u32>().ok());
            if !owner.is_some_and(crate::os::process_running) {
                let _ = dir.unlink(&entry);
            }
        }
        Ok(Scratch { dir, path, prefix: std::process::id().to_string(), written: Default::default() })
    }

    /// Write `contents` to a new private file; returns its absolute path.
    pub(crate) fn write(&self, name: &str, contents: &[u8]) -> Result<PathBuf, String> {
        let file_name = OsString::from(format!("{}-{name}", self.prefix));
        let mut file = self.dir.create_new(&file_name, modes::PRIVATE_FILE)
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
    use std::{fs, time::Duration};

    /// How often, and how long apart, `staging` retries a held lock.
    const STAGING_ATTEMPTS: usize = 100;
    const STAGING_RETRY: Duration = Duration::from_millis(10);
    /// Longer than the coarsest file-time granularity the stamp tests rely on.
    const STAMP_TICK: Duration = Duration::from_millis(20);
    /// How many ticks a stamp test waits for the file clock to move (a
    /// loaded VM can miss timer ticks).
    const STAMP_ATTEMPTS: usize = 50;
    /// Owner-writable, readable and enterable by everyone: what a
    /// permissive parent passes on.
    #[cfg(unix)]
    const LOOSE_DIR: u32 = 0o755;

    /// `staging_dir`, retried briefly: another test thread may fork a child
    /// that holds a copy of a just-released lock descriptor until it execs.
    fn staging(root: &Path) -> Staging {
        for _ in 0..STAGING_ATTEMPTS {
            if let Ok(staging) = staging_dir(root) { return staging; }
            std::thread::sleep(STAGING_RETRY);
        }
        staging_dir(root).unwrap()
    }

    /// Whether only this user can open `path` (a file or a directory).
    fn owner_only(path: &Path) -> bool {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::metadata(path).unwrap().permissions().mode() & crate::modes::GROUP_OTHER_BITS == 0
        }
        #[cfg(windows)]
        {
            use std::os::windows::{fs::OpenOptionsExt, io::AsRawHandle};
            use windows_sys::Win32::Storage::FileSystem::{FILE_FLAG_BACKUP_SEMANTICS, READ_CONTROL};
            let file = fs::OpenOptions::new().access_mode(READ_CONTROL).custom_flags(FILE_FLAG_BACKUP_SEMANTICS).open(path).unwrap();
            crate::os::is_private(file.as_raw_handle()).unwrap()
        }
    }

    /// Give a directory the access its parent passes on.
    fn loosen(dir: &Path) {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(dir, fs::Permissions::from_mode(LOOSE_DIR)).unwrap();
        }
        #[cfg(windows)]
        assert!(std::process::Command::new("icacls").arg(dir).arg("/inheritance:e").output().unwrap().status.success());
    }

    /// A symlink (on Windows, a junction) at `link` to the directory `target`.
    fn link_dir(target: &Path, link: &Path) {
        #[cfg(unix)]
        std::os::unix::fs::symlink(target, link).unwrap();
        // `mklink` takes backslashes only.
        #[cfg(windows)]
        assert!(std::process::Command::new("cmd").args(["/c", "mklink", "/J"])
            .arg(link.to_str().unwrap().replace('/', "\\")).arg(target.to_str().unwrap().replace('/', "\\"))
            .output().unwrap().status.success());
    }

    fn remove_link(link: &Path) {
        if fs::remove_file(link).is_err() { fs::remove_dir(link).unwrap(); }
    }

    /// A fresh temporary directory, removed when the test ends.
    struct TempDir(PathBuf);

    impl TempDir {
        fn new(tag: &str) -> TempDir {
            let path = std::env::temp_dir().join(format!("transcrypt-v3-{tag}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&path);
            fs::create_dir(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn replacement_is_private_and_leaves_no_worktree_temporaries() {
        let dir = TempDir::new("replace");
        let tmp = &dir.0;
        fs::create_dir(tmp.join(".git")).unwrap();
        let sdir = tmp.join(".git/transcrypt-v3-staging");
        drop(staging(tmp));
        assert!(owner_only(&sdir));
        // A crash-leftover temporary is purged on the next use.
        fs::write(sdir.join("stale.tmp"), b"stale plaintext").unwrap();
        let staging = staging(tmp);
        // A concurrent operation cannot enter (or purge) while it is held.
        assert!(staging_dir(tmp).is_err());
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        let path = tmp.join("item.secret");
        fs::write(&path, b"ciphertext placeholder").unwrap();
        let target = open_protected(tmp, Path::new("item.secret")).unwrap();
        let (_, stamp) = target.read().unwrap();
        target.replace(&staging, b"authenticated plaintext", &stamp, true).unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"authenticated plaintext");
        assert!(owner_only(&path));
        assert_eq!(fs::read_dir(tmp).unwrap().count(), 2, "only .git and the file");
        assert_eq!(fs::read_dir(&sdir).unwrap().count(), 0);
        // A symlinked or loosely permissioned staging directory is refused.
        fs::remove_dir(&sdir).unwrap();
        link_dir(tmp, &sdir);
        assert!(staging_dir(tmp).is_err());
        remove_link(&sdir);
        fs::create_dir(&sdir).unwrap();
        loosen(&sdir);
        assert!(staging_dir(tmp).is_err());
    }

    #[test]
    fn replacement_refuses_a_file_changed_since_it_was_checked() {
        let dir = TempDir::new("stamp");
        let tmp = &dir.0;
        fs::create_dir(tmp.join(".git")).unwrap();
        let staging = staging(tmp);
        let path = tmp.join("item.secret");
        fs::write(&path, b"checked contents").unwrap();
        let target = open_protected(tmp, Path::new("item.secret")).unwrap();
        let (_, stamp) = target.read().unwrap();
        // A concurrent edit after the check, even one of the same size, as
        // soon as the file clock has moved (an edit within one tick of the
        // check is beyond any stamp: A8).
        let checked = fs::metadata(&path).unwrap().modified().unwrap();
        for _ in 0..STAMP_ATTEMPTS {
            std::thread::sleep(STAMP_TICK);
            fs::write(&path, b"edited contents!").unwrap();
            if fs::metadata(&path).unwrap().modified().unwrap() != checked { break; }
        }
        assert!(target.replace(&staging, b"replacement", &stamp, false).is_err());
        assert_eq!(fs::read(&path).unwrap(), b"edited contents!", "edit must survive");
        // So is a file replaced by a different inode.
        let (_, stamp) = target.read().unwrap();
        fs::remove_file(&path).unwrap();
        fs::write(&path, b"edited contents!").unwrap();
        assert!(target.replace(&staging, b"replacement", &stamp, false).is_err());
        assert_eq!(fs::read_dir(tmp.join(".git/transcrypt-v3-staging")).unwrap().count(), 0);
    }

    #[test]
    fn protected_parent_symlinks_cannot_redirect_lock_or_hydrate() {
        let dir = TempDir::new("parent-symlink");
        let tmp = &dir.0;
        let external = tmp.join("external");
        fs::create_dir(&external).unwrap();
        fs::write(external.join("item.secret"), b"test").unwrap();
        let checkout = tmp.join("checkout");
        fs::create_dir_all(checkout.join(".git")).unwrap();
        link_dir(&external, &checkout.join("linked"));
        assert!(open_protected(&checkout, Path::new("linked/item.secret")).is_err());
        #[cfg(unix)]
        std::os::unix::fs::symlink(external.join("item.secret"), checkout.join("leaf.secret")).unwrap();
        #[cfg(windows)] // Needs Developer Mode or an administrator.
        std::os::windows::fs::symlink_file(external.join("item.secret"), checkout.join("leaf.secret")).unwrap();
        assert!(open_protected(&checkout, Path::new("leaf.secret")).is_err());
        fs::create_dir(checkout.join("regular")).unwrap();
        fs::write(checkout.join("regular/item.secret"), b"test").unwrap();
        let target = open_protected(&checkout, Path::new("regular/item.secret")).unwrap();
        let (contents, stamp) = target.read().unwrap();
        assert_eq!(*contents, b"test");
        // Race: after resolution, the parent is swapped for a symlink (on
        // Windows, a junction) to an outside directory. The held directory
        // handle keeps the write inside.
        let staging = staging(&checkout);
        fs::rename(checkout.join("regular"), checkout.join("moved")).unwrap();
        link_dir(&external, &checkout.join("regular"));
        target.replace(&staging, b"plaintext", &stamp, false).unwrap();
        assert_eq!(fs::read(external.join("item.secret")).unwrap(), b"test", "write escaped");
        assert_eq!(fs::read(checkout.join("moved/item.secret")).unwrap(), b"plaintext");
    }
}
