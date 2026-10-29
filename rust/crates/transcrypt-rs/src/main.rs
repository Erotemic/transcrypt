//! The `transcrypt-rs` command: the effectful adapter around the verified
//! core (`transcrypt-v3-core`), outside the Aeneas proof boundary.
//!
//! - `main.rs`: command dispatch, the passphrase and the public config.
//! - `filter.rs`: the clean and smudge filters; `process.rs`: Git's
//!   long-running filter protocol around them.
//! - `lifecycle.rs`: `verify-index`, the pre-commit hook, `hydrate` and
//!   `lock`, the steps whose order the Lean models follow.
//! - `credential.rs`: the unlocked key (stored by default, or held by the
//!   private-mode agent in `session.rs`).
//! - `git.rs`: every Git subprocess (bounded), object reads by verified id,
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
mod credential;
mod diff;
mod filter;
#[cfg_attr(windows, path = "fsat_windows.rs")]
mod fsat;
mod git;
mod lifecycle;
mod merge;
mod migrate;
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

/// Options of the commands that take a passphrase.
pub(crate) struct Options {
    pub(crate) password_stdin: bool,
    pub(crate) private: bool,
    pub(crate) hydrate: bool,
    /// `reencrypt`: the user already reviewed what will be trusted.
    pub(crate) yes: bool,
    /// Private mode: forget the key after this long without use.
    pub(crate) timeout: Option<std::time::Duration>,
    pub(crate) patterns: Vec<OsString>,
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
        // Also runs keyless in a bare repository (a server's pre-receive
        // hook), where there is no worktree and no key.
        let (root, keyed) = match repo_root() {
            Ok(root) => (root, true),
            Err(_) => (env::current_dir().map_err(|_| "cannot read working directory")?, false),
        };
        env::set_current_dir(&root).map_err(|_| "cannot enter repository root")?;
        let mut revs = &args[1..];
        let mut max_commits = None;
        if let Some(limit) = revs.first().and_then(|a| a.to_str()).and_then(|a| a.strip_prefix("--max-commits=")) {
            max_commits = Some(limit.parse::<usize>().map_err(|_| "--max-commits takes a number")?);
            revs = &revs[1..];
        }
        let audited = audit(&root, revs, keyed, max_commits)?;
        println!("audit: {} protected record(s) checked{}", audited.records,
            if audited.authenticated { ", all authenticated with the key" }
            else { " (envelopes only: unlock to authenticate them)" });
        return Ok(());
    }
    let root = repo_root()?;
    // File arguments (the merge driver's) are relative to where Git ran us.
    let invoked_in = env::current_dir().map_err(|_| "cannot read working directory")?;
    // All v3 paths, including the agent's short relative socket address,
    // are interpreted from the repository root.
    env::set_current_dir(&root).map_err(|_| "cannot enter repository root")?;
    let file = |arg: &OsString| invoked_in.join(arg);
    match action {
        "status" | "doctor" | "filter-process" | "lock" | "flush" | "check-encrypted" | "verify-index"
            | "pre-commit" | "serve" | "uninstall" if args.len() > 1 => Err(format!("{action} takes no arguments")),
        "status" => status(&root),
        "doctor" => doctor(&root),
        "filter-process" => process::serve(&root),
        "lock" => lock(&root),
        "flush" => flush(&root),
        "check-encrypted" => worktree_encrypted(&root, &load_config(&root)?),
        "verify-index" => verify_index_command(&root),
        "pre-commit" => pre_commit(&root),
        "serve" => session::serve(&root, &load_config(&root)?),
        "uninstall" => uninstall(&root),
        "hydrate" => match &args[1..] {
            [] => hydrate(&root).map(|n| eprintln!("Decrypted {n} file(s).")),
            [flag] if flag == "--auto" => auto_hydrate(&root),
            _ => Err("hydrate takes no arguments".into()),
        },
        "init" | "unlock" | "rekey" | "migrate" | "reencrypt" => {
            let mut options = Options { password_stdin: false, private: false, hydrate: true, timeout: None, yes: false,
                patterns: Vec::new() };
            for arg in &args[1..] {
                match (arg.to_str(), action) {
                    (Some("--password-stdin"), _) => options.password_stdin = true,
                    (Some("--private"), "init" | "unlock" | "migrate") => options.private = true,
                    (Some("--no-hydrate"), "unlock") => options.hydrate = false,
                    (Some("--yes"), "reencrypt") => options.yes = true,
                    (Some(flag), "init" | "unlock") if flag.starts_with("--timeout=") => {
                        options.timeout = Some(parse_duration(&flag["--timeout=".len()..])?);
                    },
                    (Some(flag), _) if flag.starts_with('-') => return Err(format!("{action}: unknown option {flag}")),
                    (_, "init") => options.patterns.push(arg.clone()),
                    _ => return Err(format!("{action}: unexpected argument {}", arg.to_string_lossy())),
                }
            }
            if options.timeout.is_some() && !options.private {
                return Err("--timeout applies to the private mode: use it with --private".into());
            }
            match action {
                "init" => init(&root, &options),
                "rekey" => rekey(&root, &options),
                "migrate" => migrate::migrate(&root, &options),
                "reencrypt" => reencrypt(&root, &options),
                _ => unlock(&root, &options),
            }
        },
        "protect" | "unprotect" => {
            if args.len() < 2 { return Err(format!("{action} takes one or more .gitattributes patterns")); }
            if action == "protect" { protect(&root, &args[1..]) } else { unprotect(&root, &args[1..]) }
        },
        "diff" => {
            // Git's external diff interface: path old-file old-hex old-mode
            // new-file new-hex new-mode [new-path rename-message].
            match &args[1..] {
                [path, old, _, _, new, _, _] => diff::diff(&root, os::os_bytes(path), &file(old), os::os_bytes(path), &file(new)),
                [path, old, _, _, new, _, _, new_path, _] =>
                    diff::diff(&root, os::os_bytes(path), &file(old), os::os_bytes(new_path), &file(new)),
                [path] => { println!("* Unmerged path {}", path.to_string_lossy()); Ok(()) },
                _ => Err("unexpected external diff arguments".into()),
            }
        },
        "merge" => {
            let [_, base, ours, theirs, path] = &args[..] else {
                return Err("merge driver takes %O %A %B %P".into());
            };
            if merge::merge(&root, &file(base), &file(ours), &file(theirs), os::os_bytes(path))? {
                Ok(())
            } else {
                Err(format!("merge conflict in {}: resolve it in the decrypted file", path.to_string_lossy()))
            }
        },
        "clean" | "smudge" => {
            if args.len() != 2 { return Err("Git filter requires exactly one %f pathname".into()); }
            let input = read_record(io::stdin())?;
            let output = Filters::new(&root).convert(action == "clean", os::os_bytes(&args[1]), input)?;
            io::stdout().write_all(&output).map_err(|_| "cannot write output".into())
        },
        "pre-push" => {
            if args.len() > 3 { return Err("pre-push takes the remote name and URL".into()); }
            pre_push(&root, args.get(1).map(OsString::as_os_str))
        },
        _ => Err(format!("unknown v3 operation; {USAGE}")),
    }
}

const USAGE: &str = "usage: transcrypt-rs init|protect|unprotect|unlock|status|doctor|lock|rekey|hydrate|\
    verify-index|audit|migrate|uninstall|help|version (clean, smudge, filter-process, diff, merge, pre-commit and \
    pre-push are invoked by Git)";

const HELP: &str = "\
transcrypt-rs: authenticated encryption of the files you choose, in Git.

Typical workflow
  transcrypt-rs init [PATTERN...]
                            create .transcrypt/config, set up .gitattributes, install the
                            filters and hooks, unlock, and protect the given patterns
  transcrypt-rs protect PATTERN...
                            encrypt the files matching each .gitattributes pattern (for
                            example .env, 'config/*.key', 'private/**'); stages the change
  transcrypt-rs unprotect PATTERN...
                            stop encrypting those files: their next commit is plaintext
  transcrypt-rs unlock      authenticate the passphrase once; the derived key is stored in
                            .git/transcrypt-v3/key and Git works normally from then on
  transcrypt-rs status      show the unlock state and each protected file
  transcrypt-rs doctor      check that filters, attributes, hooks and the staged index
                            protect this checkout (non-zero exit if anything is missing)
  transcrypt-rs lock        replace plaintext by the committed ciphertext and forget the key;
                            refuses if any protected file has uncommitted changes
  transcrypt-rs rekey       change the passphrase: a new config and every protected file
                            re-encrypted, staged for you to commit
  transcrypt-rs reencrypt [--yes]
                            re-encrypt staged files still encrypted under an earlier config
                            (cherry-picked or rebased across a rekey): lists them with the
                            commits that brought them, asks for that config's passphrase
  transcrypt-rs audit [<rev-list args>]
                            check, without the key, that every protected file in the given
                            commits (default HEAD) is v3 ciphertext; authenticates them when
                            unlocked. The pre-push hook runs it on the commits being pushed;
                            run it in CI or a server hook to enforce it for everyone
  transcrypt-rs uninstall   lock, then remove the filters and hooks from this checkout
  transcrypt-rs migrate     convert a repository protected by Bash transcrypt (v2): run it
                            where Bash transcrypt has decrypted the files; keeps your patterns
  transcrypt-rs version     print the version (and, for release builds, the source commit)

Options
  --password-stdin          (init, unlock, rekey, migrate, reencrypt) read the passphrase from stdin
                            instead of the terminal (where a new one is asked for twice)
  --private                 (init, unlock, migrate) keep the key only in memory (a background
                            agent, until lock or logout) and decrypted files private (0600)
  --timeout=DURATION        (init, unlock, with --private) forget the key after that long
                            without use (90s, 15m, 2h); decrypted files stay until `lock`
  --no-hydrate              (unlock) leave ciphertext in the worktree

A file is protected when its .gitattributes pattern says `transcrypt` (or sets
filter=transcrypt-v3). Each one is encrypted with AES-256-SIV under a key derived
by Argon2id from the passphrase, bound to the repository config and its exact
Git path. While unlocked, `git diff` shows decrypted changes, merges work like
text, and `git mv` is re-encrypted for the new name when you commit. Equal
plaintexts at the same path give equal ciphertexts. Filenames, sizes and
history structure are public. See docs/verification/V3-USER-GUIDE.md.";

/// A positive duration: a number with an optional unit `s`, `m` (the
/// default) or `h`.
fn parse_duration(text: &str) -> Result<std::time::Duration, String> {
    let (number, unit) = match text.char_indices().find(|(_, c)| !c.is_ascii_digit()) {
        Some((i, _)) => text.split_at(i),
        None => (text, "m"),
    };
    let scale = match unit { "s" => 1, "m" => 60, "h" => 3600, _ => 0 };
    match number.parse::<u64>() {
        Ok(n) if n > 0 && scale > 0 => Ok(std::time::Duration::from_secs(n.saturating_mul(scale))),
        _ => Err(format!("--timeout takes a positive duration such as 90s, 15m or 2h (got {text:?})")),
    }
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The public config in force: the worktree's `.transcrypt/config` (read
/// without following symlinks), or the staged one when a sparse checkout
/// leaves `.transcrypt/` out of the worktree.
pub(crate) fn load_config(root: &Path) -> Result<Vec<u8>, String> {
    let unsafe_config = |_| "unsafe .transcrypt/config (a symlink or not a regular file)".to_owned();
    let bytes = match find_protected(root, Path::new(".transcrypt/config")).map_err(unsafe_config)? {
        Some(file) => file.read()?.0.to_vec(),
        None if fs::symlink_metadata(root.join(".transcrypt")).is_ok() => {
            return Err("missing committed .transcrypt/config".into());
        },
        None => match indexed_files(root)?.into_iter().find(|e| e.path == b".transcrypt/config" && e.regular) {
            Some(staged) => git_blob(root, &staged.oid)?,
            None => return Err("missing .transcrypt directory: run init or clone a v3 repository".into()),
        },
    };
    transcrypt_v3_core::parse_config(&bytes).map_err(|_| "invalid v3 config grammar")?;
    Ok(bytes)
}

/// Read the passphrase. A new one (`init`, `rekey`) typed on a terminal is
/// asked for twice: a typo would otherwise encrypt everything under a
/// passphrase nobody knows.
pub(crate) fn passphrase(from_stdin: bool, new: bool) -> Result<Zeroizing<Vec<u8>>, String> {
    // Preallocated and wrapped before reading, so the buffer never grows
    // (leaving unwiped copies) and every exit path wipes it.
    let bytes = if from_stdin {
        let mut value = Zeroizing::new(Vec::with_capacity(4098));
        io::stdin().take(4097).read_to_end(&mut value).map_err(|_| "cannot read passphrase from stdin")?;
        if value.len() > 4096 {
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
        if new && value.len() >= 16 && *prompt("Repeat the passphrase: ")? != *value {
            return Err("the passphrases differ".into());
        }
        value
    };
    if bytes.len() < 16 { return Err("v3 requires a passphrase of at least 16 bytes".into()); }
    if new && bytes.iter().any(|b| *b == b'\n' || *b == b'\r') {
        return Err("a new passphrase must be one line (give it once on stdin)".into());
    }
    Ok(bytes)
}
