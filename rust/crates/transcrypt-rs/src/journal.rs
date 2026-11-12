//! What an interrupted command needs to be completed or undone exactly,
//! recorded in this checkout's Git directory before the command changes
//! anything (a linked worktree has its own index, so each has its own):
//!
//! - `transcrypt-v3-setup`: what `init` or `migrate` was asked to protect.
//!   Resuming an interrupted one keeps it, whatever the rerun names.
//! - `transcrypt-v3-rekey`: rekey's journal, each index entry it replaces
//!   as it was and as it becomes, for `rekey --continue` and `--abort`.
//!
//! Both are shared with transcrypt-bash, byte for byte: NUL-terminated
//! fields, the first naming the format, written whole by a rename.

use std::{fs, io::Write, path::PathBuf};
use crate::git::{Mode, ObjectId, Repository};

/// The setup record's file.
pub(crate) const SETUP_FILE: &str = "transcrypt-v3-setup";
const SETUP_MAGIC: &[u8] = b"transcrypt-v3-setup 1";
/// The rekey journal's file.
const REKEY_FILE: &str = "transcrypt-v3-rekey";
const REKEY_MAGIC: &[u8] = b"transcrypt-v3-rekey 1";

/// What an interrupted `rekey` left, and how to finish or undo it.
pub(crate) const REKEY_PENDING: &str = "an interrupted rekey: finish it with `transcrypt-rs rekey --continue` \
    (the new passphrase) or undo it with `transcrypt-rs rekey --abort` (the old one); either changes only what \
    the rekey staged";

fn path(repo: &Repository, name: &str) -> PathBuf {
    repo.git_dir().join(name)
}

/// Write `fields`, each NUL-terminated, to `name` in the Git directory,
/// atomically (a temporary file renamed over it).
fn write_fields(repo: &Repository, name: &str, fields: &[&[u8]]) -> Result<(), String> {
    let file = path(repo, name);
    if fs::symlink_metadata(&file).is_ok_and(|m| m.file_type().is_symlink()) {
        return Err(format!("refusing a symlinked {}", file.display()));
    }
    let temporary = path(repo, &format!("{name}.{}", std::process::id()));
    let fail = |e: std::io::Error| format!("cannot write {}: {e}", file.display());
    let mut out = fs::File::create(&temporary).map_err(fail)?;
    for field in fields {
        out.write_all(field).and_then(|()| out.write_all(&[0])).map_err(fail)?;
    }
    out.sync_all().map_err(fail)?;
    drop(out);
    fs::rename(&temporary, &file).map_err(|e| {
        let _ = fs::remove_file(&temporary);
        fail(e)
    })
}

/// The fields of `name` in the Git directory, if it exists; an error if it
/// is not a regular file or does not end with a complete field.
fn read_fields(repo: &Repository, name: &str) -> Result<Option<Vec<Vec<u8>>>, String> {
    let file = path(repo, name);
    let Ok(meta) = fs::symlink_metadata(&file) else { return Ok(None) };
    if !meta.is_file() {
        return Err(format!("unusable {}", file.display()));
    }
    let bytes = fs::read(&file).map_err(|e| format!("cannot read {}: {e}", file.display()))?;
    let Some(body) = bytes.strip_suffix(&[0]) else {
        return Err(format!("{} is truncated", file.display()));
    };
    Ok(Some(body.split(|b| *b == 0).map(<[u8]>::to_vec).collect()))
}

fn remove(repo: &Repository, name: &str) -> Result<(), String> {
    match fs::remove_file(path(repo, name)) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => Err(format!("cannot remove .git/{name}: {e}")),
        _ => Ok(()),
    }
}

/// The command a setup record is for.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum SetupKind {
    Init,
    Migrate,
}

impl SetupKind {
    fn name(self) -> &'static [u8] {
        match self { SetupKind::Init => b"init", SetupKind::Migrate => b"migrate" }
    }
}

/// What `init` (its patterns, as given) or `migrate` (the paths it
/// converts) was asked to protect, and whether it finished (`complete`: a
/// fresh setup then ignores it).
pub(crate) struct SetupRecord {
    pub(crate) kind: SetupKind,
    pub(crate) complete: bool,
    pub(crate) items: Vec<Vec<u8>>,
}

impl SetupRecord {
    pub(crate) fn load(repo: &Repository) -> Result<Option<SetupRecord>, String> {
        let Some(fields) = read_fields(repo, SETUP_FILE)? else { return Ok(None) };
        let unrecognized = || format!("unrecognized .git/{SETUP_FILE}; to start over: {}", crate::setup::START_OVER);
        let [magic, kind, state, items @ ..] = &fields[..] else { return Err(unrecognized()) };
        if magic != SETUP_MAGIC { return Err(unrecognized()); }
        let kind = match &kind[..] {
            b"init" => SetupKind::Init,
            b"migrate" => SetupKind::Migrate,
            _ => return Err(unrecognized()),
        };
        let complete = match &state[..] {
            b"started" => false,
            b"complete" => true,
            _ => return Err(unrecognized()),
        };
        Ok(Some(SetupRecord { kind, complete, items: items.to_vec() }))
    }

    pub(crate) fn save(&self, repo: &Repository) -> Result<(), String> {
        let state: &[u8] = if self.complete { b"complete" } else { b"started" };
        let mut fields: Vec<&[u8]> = vec![SETUP_MAGIC, self.kind.name(), state];
        fields.extend(self.items.iter().map(Vec::as_slice));
        write_fields(repo, SETUP_FILE, &fields)
    }

    pub(crate) fn remove(repo: &Repository) -> Result<(), String> {
        remove(repo, SETUP_FILE)
    }
}

/// One index entry rekey replaces: its mode, and its object before and
/// after.
pub(crate) struct JournalEntry {
    pub(crate) mode: Mode,
    pub(crate) old: ObjectId,
    pub(crate) new: ObjectId,
    pub(crate) path: Vec<u8>,
}

/// rekey's journal: the old config (the worktree's, which the old
/// passphrase opens) and the new one, by object id, and every index entry
/// it replaces (each protected file, and `.transcrypt/config`).
pub(crate) struct RekeyJournal {
    pub(crate) old_config: ObjectId,
    pub(crate) new_config: ObjectId,
    pub(crate) entries: Vec<JournalEntry>,
}

/// Fields per journal entry: mode, old id, new id, path.
const ENTRY_FIELDS: usize = 4;

impl RekeyJournal {
    pub(crate) fn pending(repo: &Repository) -> bool {
        fs::symlink_metadata(path(repo, REKEY_FILE)).is_ok()
    }

    pub(crate) fn load(repo: &Repository) -> Result<Option<RekeyJournal>, String> {
        let Some(fields) = read_fields(repo, REKEY_FILE)? else { return Ok(None) };
        let unrecognized = || format!("unrecognized .git/{REKEY_FILE}");
        let [magic, old_config, new_config, entries @ ..] = &fields[..] else { return Err(unrecognized()) };
        if magic != REKEY_MAGIC || entries.len() % ENTRY_FIELDS != 0 { return Err(unrecognized()); }
        let oid = |bytes: &[u8]| ObjectId::new(bytes).ok_or_else(unrecognized);
        let entries = entries.chunks(ENTRY_FIELDS).map(|e| Ok(JournalEntry {
            mode: Mode::parse_regular(&e[0]).ok_or_else(unrecognized)?,
            old: oid(&e[1])?,
            new: oid(&e[2])?,
            path: e[3].clone(),
        })).collect::<Result<Vec<_>, String>>()?;
        Ok(Some(RekeyJournal { old_config: oid(old_config)?, new_config: oid(new_config)?, entries }))
    }

    pub(crate) fn save(&self, repo: &Repository) -> Result<(), String> {
        let modes: Vec<String> = self.entries.iter().map(|e| e.mode.to_string()).collect();
        let mut fields: Vec<&[u8]> = vec![REKEY_MAGIC, self.old_config.as_str().as_bytes(), self.new_config.as_str().as_bytes()];
        for (entry, mode) in self.entries.iter().zip(&modes) {
            fields.extend([mode.as_bytes(), entry.old.as_str().as_bytes(), entry.new.as_str().as_bytes(), &entry.path]);
        }
        write_fields(repo, REKEY_FILE, &fields)
    }

    pub(crate) fn remove(repo: &Repository) -> Result<(), String> {
        remove(repo, REKEY_FILE)
    }
}
