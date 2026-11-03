//! The `transcrypt-rs` command: the effectful adapter around the verified
//! core (`transcrypt-v3-core`), outside the Aeneas proof boundary.
//!
//! - `main.rs`: command dispatch, the passphrase and the public config;
//!   `cli.rs`: the command line, parsed into a `Command`.
//! - `filter.rs`: the clean and smudge filters; `process.rs`: Git's
//!   long-running filter protocol around them.
//! - `lifecycle.rs`: `verify-index`, the pre-commit hook, `hydrate` and
//!   `lock`, the steps whose order the Lean models follow.
//! - `credential.rs`: the unlocked key (stored by default, or held by the
//!   private-mode agent in `session.rs`).
//! - `git/`: the `Repository` (found once, passed explicitly), every Git
//!   subprocess (bounded), object reads by verified id,
//!   listings and attribute answers parsed by the verified core.
//! - `worktree.rs`: race-free worktree access and private staging;
//!   `fsat.rs` (`fsat_windows.rs`): directory-relative I/O.
//! - `os_unix.rs` (`os_windows.rs`): the other OS primitives.
//! - `setup.rs`: init, unlock, uninstall, filters and hooks, `status` and
//!   `doctor`.
//! - `attributes.rs`: the `transcrypt` macro, `protect` and `unprotect`.
//! - `rekey.rs`: `rekey` and `reencrypt`; `migrate.rs`: from Bash transcrypt.
//! - `audit.rs`: keyless history audit and the pre-push hook.
//! - `merge.rs` and `diff.rs`: the merge and diff drivers for protected files.
#[cfg(not(any(unix, windows)))]
compile_error!("transcrypt-rs requires Unix or Windows");

use std::{
    env, fs,
    ffi::OsString,
    io::{self, Read, Write},
    path::Path,
    process::ExitCode,
};
use zeroize::Zeroizing;
mod attributes;
mod audit;
mod cli;
mod credential;
mod diff;
mod filter;
#[cfg_attr(windows, path = "fsat_windows.rs")]
mod fsat;
mod git;
mod lifecycle;
mod listing;
mod merge;
mod migrate;
mod modes;
#[cfg_attr(unix, path = "os_unix.rs")]
#[cfg_attr(windows, path = "os_windows.rs")]
mod os;
mod process;
mod rekey;
mod session;
mod setup;
mod worktree;
use attributes::{protect, unprotect};
use audit::*;
use cli::{AuditArgs, Command, DiffArgs, MergeArgs, HELP, USAGE};
use filter::Filters;
use rekey::{reencrypt, rekey};
use git::*;
use lifecycle::*;
use setup::*;
use worktree::*;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("transcrypt-rs: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    // Git substitutes `%f` as a single shell-quoted argument. Preserve raw
    // Unix pathname bytes: env::args() would reject valid non-UTF8 Git paths.
    let args: Vec<OsString> = env::args_os().skip(1).collect();
    let action = args.first().and_then(|x| x.to_str()).ok_or(USAGE)?;
    if matches!(action, "help" | "--help" | "-h") {
        println!("{HELP}");
        return Ok(());
    }
    if matches!(action, "version" | "--version" | "-V") {
        // Release builds (scripts/build-release.sh) record their commit.
        match option_env!("TRANSCRYPT_RS_COMMIT") {
            Some(commit) => println!("transcrypt-rs {} ({commit})", env!("CARGO_PKG_VERSION")),
            None => println!("transcrypt-rs {}", env!("CARGO_PKG_VERSION")),
        }
        return Ok(());
    }
    os::harden_process()?;
    if action != "serve" {
        // The agent keeps ignoring SIGPIPE: a client may hang up mid-reply.
        os::default_sigpipe();
    }
    if action == "audit" {
        return run_audit(AuditArgs::parse(&args[1..])?);
    }
    // A command's arguments are refused only once the repository is found.
    let command = Command::parse(action, &args[1..]);
    // Found once, and passed to everything that needs it. The current
    // directory stays where Git ran us: Git commands run in the repository's
    // root, and the drivers' file arguments are relative to here.
    let repo = Repository::discover()?;
    match command? {
        Command::Status => status(&repo),
        Command::Doctor => doctor(&repo),
        Command::FilterProcess => process::serve(&repo),
        Command::Lock => lock(&repo),
        Command::Flush => flush(&repo),
        Command::CheckEncrypted => worktree_encrypted(&repo, &load_config(&repo)?),
        Command::VerifyIndex => verify_index_command(&repo),
        Command::PreCommit => pre_commit(&repo),
        Command::Serve => session::serve(&repo, &load_config(&repo)?),
        Command::Uninstall => uninstall(&repo),
        Command::Hydrate { auto: false } => hydrate(&repo).map(|n| eprintln!("Decrypted {n} file(s).")),
        Command::Hydrate { auto: true } => auto_hydrate(&repo),
        Command::Init(args) => init(&repo, &args),
        Command::Unlock(args) => unlock(&repo, &args),
        Command::Rekey { password_stdin } => rekey(&repo, password_stdin),
        Command::Migrate(args) => migrate::migrate(&repo, &args),
        Command::Reencrypt(args) => reencrypt(&repo, &args),
        Command::Protect(patterns) => protect(&repo, &patterns),
        Command::Unprotect(patterns) => unprotect(&repo, &patterns),
        Command::Diff(DiffArgs { old_path, old, new_path, new }) =>
            diff::diff(&repo, os::os_bytes(&old_path), Path::new(&old), os::os_bytes(&new_path), Path::new(&new)),
        Command::DiffUnmerged { path } => {
            println!("* Unmerged path {}", path.to_string_lossy());
            Ok(())
        },
        Command::Merge(MergeArgs { base, ours, theirs, path }) => {
            if merge::merge(&repo, Path::new(&base), Path::new(&ours), Path::new(&theirs), os::os_bytes(&path))? {
                Ok(())
            } else {
                Err(format!("merge conflict in {}: resolve it in the decrypted file", path.to_string_lossy()))
            }
        },
        Command::Filter { clean, path } => {
            let input = read_record(io::stdin())?;
            let output = Filters::new(&repo).convert(clean, os::os_bytes(&path), input)?;
            io::stdout().write_all(&output).map_err(|_| "cannot write output".into())
        },
        Command::PrePush { remote } => pre_push(&repo, remote.as_deref()),
    }
}

/// `audit`. Also runs keyless in a bare repository (a server's pre-receive
/// hook), where there is no worktree and no key.
fn run_audit(AuditArgs { max_commits, revs }: AuditArgs) -> Result<(), String> {
    let (repo, keyed) = match Repository::discover() {
        Ok(repo) => (repo, true),
        Err(_) => (Repository::discover_bare()?, false),
    };
    let audited = audit(&repo, &revs, keyed, max_commits)?;
    println!("audit: {} protected record(s) checked{}", audited.records,
        if audited.authenticated { ", all authenticated with the key where one was needed, as is every record at an unprotected path" }
        else { " (envelopes only: unlock to authenticate them and any record at an unprotected path)" });
    Ok(())
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Bytes of a config id shown to identify it to people.
const SHORT_ID_LEN: usize = 4;

/// A config id as shown to people: the hex of its first bytes.
pub(crate) fn short_id(id: &[u8]) -> String {
    hex(&id[..SHORT_ID_LEN])
}

/// The public config in force: the worktree's `.transcrypt/config` (read
/// without following symlinks), or the staged one when a sparse checkout
/// leaves `.transcrypt/` out of the worktree.
pub(crate) fn load_config(repo: &Repository) -> Result<Vec<u8>, String> {
    let unsafe_config = |_| "unsafe .transcrypt/config (a symlink or not a regular file)".to_owned();
    let bytes = match find_protected(repo.root(), Path::new(CONFIG_PATH)).map_err(unsafe_config)? {
        Some(file) => file.read()?.0.to_vec(),
        None if fs::symlink_metadata(repo.root().join(".transcrypt")).is_ok() => {
            return Err("missing committed .transcrypt/config".into());
        },
        None => match indexed_files(repo)?.into_iter().find(|e| e.path == CONFIG_PATH.as_bytes() && e.regular()) {
            Some(staged) => git_blob(repo, &staged.oid)?,
            None => return Err("missing .transcrypt directory: run init or clone a v3 repository".into()),
        },
    };
    transcrypt_v3_core::parse_config(&bytes).map_err(|_| "invalid v3 config grammar")?;
    Ok(bytes)
}

/// The shortest passphrase v3 accepts, and the longest read from stdin.
const MIN_PASSPHRASE: usize = 16;
const MAX_PASSPHRASE: usize = 4096;

/// Read the passphrase. A new one (`init`, `rekey`) typed on a terminal is
/// asked for twice: a typo would otherwise encrypt everything under a
/// passphrase nobody knows.
pub(crate) fn passphrase(from_stdin: bool, new: bool) -> Result<Zeroizing<Vec<u8>>, String> {
    // Preallocated and wrapped before reading, so the buffer never grows
    // (leaving unwiped copies) and every exit path wipes it.
    let bytes = if from_stdin {
        let mut value = Zeroizing::new(Vec::with_capacity(MAX_PASSPHRASE + b"\r\n".len()));
        io::stdin().take(MAX_PASSPHRASE as u64 + 1).read_to_end(&mut value)
            .map_err(|_| "cannot read passphrase from stdin")?;
        if value.len() > MAX_PASSPHRASE {
            return Err("passphrase too long".into());
        }
        if value.last() == Some(&b'\n') { value.pop(); }
        if value.last() == Some(&b'\r') { value.pop(); }
        value
    } else {
        let prompt = |text: &str| rpassword::prompt_password(text)
            .map(|p| Zeroizing::new(p.into_bytes()))
            .map_err(|e| format!("cannot read terminal passphrase: {e}"));
        let value = prompt(if new { "New transcrypt v3 passphrase: " } else { "Transcrypt v3 passphrase: " })?;
        // A passphrase too short to accept is refused below without asking
        // for it again.
        if new && value.len() >= MIN_PASSPHRASE && *prompt("Repeat the passphrase: ")? != *value {
            return Err("the passphrases differ".into());
        }
        value
    };
    if bytes.len() < MIN_PASSPHRASE {
        return Err(format!("v3 requires a passphrase of at least {MIN_PASSPHRASE} bytes"));
    }
    if new && bytes.iter().any(|b| *b == b'\n' || *b == b'\r') {
        return Err("a new passphrase must be one line (give it once on stdin)".into());
    }
    Ok(bytes)
}
