//! External diff driver for protected files (`diff=transcrypt-v3`, set by
//! the `transcrypt` attribute macro): show the difference between
//! the decrypted versions. A side that is a v3 record is authenticated at its
//! own Git path (Git passes the full path, which a textconv filter would not
//! get); a side that is plaintext (the worktree) is shown as is. Nothing is
//! cached, unlike a textconv cache, which would keep plaintext in
//! `refs/notes`.

use std::{fs, io::{self, Write}, path::Path, process::Command};
use transcrypt_v3_core::{record_envelope_ok, MAX_RECORD};
use zeroize::Zeroizing;
use crate::{
    credential::Key,
    git::{read_record, run_bounded_status},
    load_config,
    worktree::Scratch,
};

/// Print the diff of one protected file between `old` (at `old_path`) and
/// `new` (at `new_path`), as Git's external diff interface supplies them.
pub(crate) fn diff(root: &Path, old_path: &[u8], old: &Path, new_path: &[u8], new: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    let id = transcrypt_rs::config_id(&config);
    let key = Key::load(root, &config)?;
    // `None`: an encrypted side that cannot be opened while locked.
    let side = |file: &Path, path: &[u8]| -> Result<Option<Zeroizing<Vec<u8>>>, String> {
        let input = fs::File::open(file).map_err(|_| "cannot read a diff input")?;
        let bytes = read_record(input)?;
        if !record_envelope_ok(&bytes, &id) { return Ok(Some(bytes)); }
        let Some(key) = &key else { return Ok(None) };
        // A staged `git mv` still holds the record of the old path, which
        // the pre-commit hook re-encrypts; show it decrypted meanwhile.
        key.open(path, &bytes).or_else(|e| if path != old_path { key.open(old_path, &bytes) } else { Err(e) })
            .map(Some).map_err(|e| format!("{}: {e}", String::from_utf8_lossy(path)))
    };
    let (a_label, b_label) = (format!("a/{}", String::from_utf8_lossy(old_path)),
        format!("b/{}", String::from_utf8_lossy(new_path)));
    let (Some(a), Some(b)) = (side(old, old_path)?, side(new, new_path)?) else {
        println!("Binary files {a_label} and {b_label} differ (unlock to see the decrypted diff)");
        return Ok(());
    };
    let scratch = Scratch::create(root)?;
    let (a, b) = (scratch.write("a", &a)?, scratch.write("b", &b)?);
    let mut command = Command::new("diff");
    command.args(["-u", "-L", &a_label, "-L", &b_label]).arg(&a).arg(&b).current_dir(root);
    // At most both inputs, each line once more for its marker.
    let (status, output, _) = run_bounded_status(command, None, 4 * MAX_RECORD)?;
    drop(scratch);
    match status.code() {
        Some(0 | 1) => io::stdout().write_all(&output).map_err(|_| "cannot write the diff".into()),
        _ => Err("diff failed".into()),
    }
}
