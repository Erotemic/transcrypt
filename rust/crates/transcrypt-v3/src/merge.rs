//! Git merge driver for protected files (`merge=transcrypt-v3`, set by the
//! `transcrypt` attribute macro): decrypt base, ours and theirs, merge
//! the plaintexts with `git merge-file` in a private `Scratch` directory, and store
//! the result (conflict markers included) encrypted again. A conflicted
//! secret is then resolved in plaintext like any other file.

use std::{fs, path::Path};
use transcrypt_v3_core::MAX_RECORD;
use zeroize::Zeroizing;
use crate::{
    credential::Key,
    git::{git_command, read_limited, run_bounded_status},
    worktree::Scratch,
    load_config,
};

/// Merge one protected file. `Ok(true)` for a clean merge, `Ok(false)` when
/// the stored result has conflict markers. On any error `ours` is left as
/// it was, which Git records as a conflict.
pub(crate) fn merge(root: &Path, base: &Path, ours: &Path, theirs: &Path, git_path: &[u8]) -> Result<bool, String> {
    transcrypt_v3::validate_protected_path(git_path)?;
    let config = load_config(root)?;
    let key = Key::require(root, &config).map_err(|e| format!("{e} to merge protected files"))?;
    let decrypt = |file: &Path, required: bool| -> Result<Zeroizing<Vec<u8>>, String> {
        let input = fs::File::open(file).map_err(|_| "cannot read a merge input")?;
        let record = read_limited(input, MAX_RECORD)?;
        if record.is_empty() { return Ok(Zeroizing::new(Vec::new())); }
        match key.open(git_path, &record) {
            Ok(plaintext) => Ok(plaintext),
            // A base that does not open here only makes conflicts more likely.
            Err(_) if !required => Ok(Zeroizing::new(Vec::new())),
            Err(e) => Err(e),
        }
    };
    let inputs = [decrypt(ours, true)?, decrypt(base, false)?, decrypt(theirs, true)?];
    let scratch = Scratch::create(root)?;
    let mut command = git_command(Some(root));
    command.args(["merge-file", "-p", "-L", "ours", "-L", "base", "-L", "theirs"]);
    for (name, plaintext) in ["ours", "base", "theirs"].iter().zip(&inputs) {
        command.arg(scratch.write(name, plaintext)?);
    }
    let result = run_bounded_status(command, None, 3 * MAX_RECORD);
    drop(scratch);
    let (status, merged, errors) = result?;
    let conflicts = match status.code() {
        Some(0) => false,
        Some(n) if n > 0 => true,
        _ => return Err(format!("git merge-file failed: {}", String::from_utf8_lossy(&errors))),
    };
    let record = key.clean(git_path, &merged)?;
    fs::write(ours, &*record).map_err(|_| "cannot write the merge result")?;
    Ok(!conflicts)
}
