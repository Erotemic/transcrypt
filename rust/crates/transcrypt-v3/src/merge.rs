//! Git merge driver for protected files (`merge=transcrypt-v3`, set for this
//! checkout in `.git/info/attributes`): decrypt base, ours and theirs, merge
//! the plaintexts with `git merge-file` in a private directory, and store
//! the result (conflict markers included) encrypted again. A conflicted
//! secret is then resolved in plaintext like any other file.

use std::{
    ffi::{OsStr, OsString},
    fs,
    io::{self, Write},
    path::Path,
};
use transcrypt_v3_core::MAX_RECORD;
use zeroize::Zeroizing;
use crate::{
    fsat,
    git::{git_command, read_limited, run_bounded_status},
    load_config,
    session::{self, Operation},
};

/// Merge one protected file. `Ok(true)` for a clean merge, `Ok(false)` when
/// the stored result has conflict markers. On any error `ours` is left as
/// it was, which Git records as a conflict.
pub(crate) fn merge(root: &Path, base: &Path, ours: &Path, theirs: &Path, git_path: &[u8]) -> Result<bool, String> {
    transcrypt_v3::validate_protected_path(git_path)?;
    let config = load_config(root)?;
    session::request(root, &config, Operation::Ping, &[], &[])
        .map_err(|_| "unlock to merge protected files")?;
    let decrypt = |file: &Path, required: bool| -> Result<Zeroizing<Vec<u8>>, String> {
        let input = fs::File::open(file).map_err(|_| "cannot read a merge input")?;
        let record = read_limited(input, MAX_RECORD)?;
        if record.is_empty() { return Ok(Zeroizing::new(Vec::new())); }
        match session::request(root, &config, Operation::Decrypt, git_path, &record) {
            Ok(plaintext) => Ok(plaintext),
            // A base from another path (a rename) does not open here; merging
            // against an empty base only makes conflicts more likely.
            Err(_) if !required => Ok(Zeroizing::new(Vec::new())),
            Err(e) => Err(e),
        }
    };
    let inputs = [decrypt(ours, true)?, decrypt(base, false)?, decrypt(theirs, true)?];
    let scratch = Scratch::create(root)?;
    let names = ["ours", "base", "theirs"];
    for (name, plaintext) in names.iter().zip(&inputs) {
        scratch.write(name, plaintext)?;
    }
    let mut command = git_command(Some(root));
    command.args(["merge-file", "-p", "-L", "ours", "-L", "base", "-L", "theirs"]);
    for name in names {
        command.arg(scratch.path(name));
    }
    let result = run_bounded_status(command, None, 3 * MAX_RECORD);
    scratch.remove(&names);
    let (status, merged, errors) = result?;
    let conflicts = match status.code() {
        Some(0) => false,
        Some(n) if n > 0 => true,
        _ => return Err(format!("git merge-file failed: {}", String::from_utf8_lossy(&errors))),
    };
    let record = session::request(root, &config, Operation::Encrypt, git_path, &merged)?;
    fs::write(ours, &*record).map_err(|_| "cannot write the merge result")?;
    Ok(!conflicts)
}

/// `.git/transcrypt-v3-merge`: a real mode-0700 directory for the plaintext
/// inputs of one merge, written as exclusive mode-0600 files and removed
/// afterwards.
struct Scratch {
    dir: fsat::Dir,
    prefix: String,
}

impl Scratch {
    fn create(root: &Path) -> Result<Scratch, String> {
        let git_dir = fsat::Dir::open(root).and_then(|r| r.subdir(OsStr::new(".git")))
            .map_err(|_| "cannot open .git directory")?;
        let name = OsStr::new("transcrypt-v3-merge");
        match git_dir.mkdir(name, 0o700) {
            Ok(()) => {},
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {},
            Err(e) => return Err(format!("cannot create private merge directory: {e}")),
        }
        let dir = git_dir.subdir(name).map_err(|_| "unsafe .git/transcrypt-v3-merge")?;
        if dir.mode().map_err(|_| "cannot examine private merge directory")? & 0o077 != 0 {
            return Err("unsafe .git/transcrypt-v3-merge; require a real 0700 directory".into());
        }
        // Inputs left by a merge that crashed: their process no longer runs.
        for entry in dir.entries().map_err(|_| "cannot list private merge directory")? {
            let owner = entry.to_str().and_then(|n| n.split('-').next()).and_then(|p| p.parse::<i32>().ok());
            // SAFETY: kill with signal 0 only checks whether the process exists.
            let running = owner.is_some_and(|pid| unsafe { libc::kill(pid, 0) } == 0
                || io::Error::last_os_error().raw_os_error() == Some(libc::EPERM));
            if !running {
                let _ = dir.unlink(&entry);
            }
        }
        Ok(Scratch { dir, prefix: format!("{}", std::process::id()) })
    }

    fn file(&self, name: &str) -> OsString {
        OsString::from(format!("{}-{name}", self.prefix))
    }

    fn path(&self, name: &str) -> std::path::PathBuf {
        Path::new(".git/transcrypt-v3-merge").join(self.file(name))
    }

    fn write(&self, name: &str, contents: &[u8]) -> Result<(), String> {
        let mut file = self.dir.create_new(&self.file(name), 0o600)
            .map_err(|e| format!("cannot create private merge file: {e}"))?;
        file.write_all(contents).map_err(|e| format!("cannot write private merge file: {e}"))
    }

    /// Remove the inputs (no secure-erasure claim: the directory is private
    /// to this user, and nothing is left behind once the merge returns).
    fn remove(&self, names: &[&str]) {
        for name in names {
            let _ = self.dir.unlink(&self.file(name));
        }
    }
}
