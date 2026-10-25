//! The `transcrypt-v3` command: the effectful adapter around the verified
//! core (`transcrypt-v3-core`), outside the Aeneas proof boundary.
//!
//! - `main.rs`: command dispatch, the Git filters and `status`.
//! - `lifecycle.rs`: `verify-index`, the pre-commit hook, `hydrate` and
//!   `lock`, the steps whose order the Lean models follow.
//! - `credential.rs`: the unlocked key (stored by default, or held by the
//!   private-mode agent in `session.rs`).
//! - `git.rs`: every Git subprocess (bounded), object reads by verified id,
//!   listings and attribute answers parsed by the verified core.
//! - `worktree.rs`: race-free worktree access and private staging;
//!   `fsat.rs`: dirfd I/O.
//! - `setup.rs`: init, unlock, protect, rekey, uninstall, hooks, `doctor`.
//! - `audit.rs`: keyless history audit and the pre-push hook.
//! - `process.rs`: Git's long-running filter protocol; `merge.rs` and
//!   `diff.rs`: the merge and diff drivers for protected files.
#[cfg(not(unix))]
compile_error!("transcrypt-v3 requires Unix");

use std::{
    env, fs,
    ffi::OsString,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::ExitCode,
};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;
use zeroize::Zeroizing;
mod audit;
mod credential;
mod diff;
mod fsat;
mod git;
mod lifecycle;
mod merge;
mod migrate;
mod process;
mod session;
mod setup;
mod worktree;
use credential::{Key, State};
use transcrypt_v3_core::{parse_file_header, record_envelope_ok, smudge_action, Refusal, SmudgeAction, MAX_RECORD};
use audit::*;
use git::*;
use lifecycle::*;
use setup::*;
use worktree::*;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("transcrypt-v3: {err}");
            ExitCode::FAILURE
        }
    }
}

/// Options of the commands that take a passphrase.
pub(crate) struct Options {
    pub(crate) password_stdin: bool,
    pub(crate) private: bool,
    pub(crate) hydrate: bool,
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
    session::harden_process()?;
    if action != "serve" {
        // Die quietly when a reader such as `head` closes our output, like
        // other command-line tools (Rust ignores SIGPIPE by default). The
        // agent keeps ignoring it: a client may hang up mid-reply.
        // SAFETY: setting a signal disposition to its default is always valid.
        unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) };
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
    let no_args = |name: &str| if args.len() == 1 { Ok(()) } else { Err(format!("{name} takes no arguments")) };
    match action {
        "status" => { no_args(action)?; status(&root) },
        "doctor" => { no_args(action)?; doctor(&root) },
        "init" | "unlock" | "rekey" | "migrate" | "reencrypt" => {
            let mut options = Options { password_stdin: false, private: false, hydrate: true, timeout: None,
                patterns: Vec::new() };
            for arg in &args[1..] {
                match (arg.to_str(), action) {
                    (Some("--password-stdin"), _) => options.password_stdin = true,
                    (Some("--private"), "init" | "unlock" | "migrate") => options.private = true,
                    (Some("--no-hydrate"), "unlock") => options.hydrate = false,
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
            let file = |arg: &OsString| invoked_in.join(arg);
            match &args[1..] {
                [path, old, _, _, new, _, _] => diff::diff(&root, path.as_bytes(), &file(old), path.as_bytes(), &file(new)),
                [path, old, _, _, new, _, _, new_path, _] =>
                    diff::diff(&root, path.as_bytes(), &file(old), new_path.as_bytes(), &file(new)),
                [path] => { println!("* Unmerged path {}", path.to_string_lossy()); Ok(()) },
                _ => Err("unexpected external diff arguments".into()),
            }
        },
        "merge" => {
            let [_, base, ours, theirs, path] = &args[..] else {
                return Err("merge driver takes %O %A %B %P".into());
            };
            let file = |arg: &OsString| invoked_in.join(arg);
            if merge::merge(&root, &file(base), &file(ours), &file(theirs), path.as_bytes())? {
                Ok(())
            } else {
                Err(format!("merge conflict in {}: resolve it in the decrypted file", path.to_string_lossy()))
            }
        },
        "filter-process" => { no_args(action)?; process::serve(&root) },
        "clean" | "smudge" => {
            if args.len() != 2 { return Err("Git filter requires exactly one %f pathname".into()); }
            let input = Zeroizing::new(read_limited(io::stdin(), MAX_RECORD)?);
            let output = Filters::new(&root).convert(action == "clean", args[1].as_bytes(), input)?;
            io::stdout().write_all(&output).map_err(|_| "cannot write output".into())
        },
        "pre-push" => {
            if args.len() > 3 { return Err("pre-push takes the remote name and URL".into()); }
            pre_push(&root, args.get(1).map(OsString::as_os_str))
        },
        "hydrate" if args.len() == 2 && args[1] == "--auto" => auto_hydrate(&root),
        "lock" | "verify-index" | "pre-commit" | "hydrate" | "serve" | "uninstall" | "flush" | "check-encrypted" => {
            no_args(action)?;
            match action {
                "lock" => lock(&root),
                "flush" => flush(&root),
                "check-encrypted" => worktree_encrypted(&root, &load_config(&root)?),
                "verify-index" => verify_index_command(&root),
                "pre-commit" => pre_commit(&root),
                "hydrate" => hydrate(&root).map(|n| eprintln!("Decrypted {n} file(s).")),
                "serve" => session::serve(&root, &load_config(&root)?),
                "uninstall" => uninstall(&root),
                _ => unreachable!(),
            }
        },
        _ => Err(format!("unknown v3 operation; {USAGE}")),
    }
}

const USAGE: &str = "usage: transcrypt-v3 init|protect|unprotect|unlock|status|doctor|lock|rekey|hydrate|\
    verify-index|audit|migrate|uninstall|help (clean, smudge, filter-process, diff, merge, pre-commit and \
    pre-push are invoked by Git)";

const HELP: &str = "\
transcrypt-v3: authenticated encryption of the files you choose, in Git.

Typical workflow
  transcrypt-v3 init [PATTERN...]
                            create .transcrypt/config, set up .gitattributes, install the
                            filters and hooks, unlock, and protect the given patterns
  transcrypt-v3 protect PATTERN...
                            encrypt the files matching each .gitattributes pattern (for
                            example .env, 'config/*.key', 'private/**'); stages the change
  transcrypt-v3 unprotect PATTERN...
                            stop encrypting those files: their next commit is plaintext
  transcrypt-v3 unlock      authenticate the passphrase once; the derived key is stored in
                            .git/transcrypt-v3/key and Git works normally from then on
  transcrypt-v3 status      show the unlock state and each protected file
  transcrypt-v3 doctor      check that filters, attributes, hooks and the staged index
                            protect this checkout (non-zero exit if anything is missing)
  transcrypt-v3 lock        replace plaintext by the committed ciphertext and forget the key;
                            refuses if any protected file has uncommitted changes
  transcrypt-v3 rekey       change the passphrase: a new config and every protected file
                            re-encrypted, staged for you to commit
  transcrypt-v3 reencrypt   re-encrypt staged files still encrypted under an earlier config
                            (cherry-picked or rebased across a rekey); asks for its passphrase
  transcrypt-v3 audit [<rev-list args>]
                            check, without the key, that every protected file in the given
                            commits (default HEAD) is v3 ciphertext; authenticates them when
                            unlocked. The pre-push hook runs it on the commits being pushed;
                            run it in CI or a server hook to enforce it for everyone
  transcrypt-v3 uninstall   lock, then remove the filters and hooks from this checkout
  transcrypt-v3 migrate     convert a repository protected by Bash transcrypt (v2): run it
                            where Bash transcrypt has decrypted the files; keeps your patterns

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

/// The clean and smudge filters of one Git process (one file, or every file
/// of a Git command for `filter-process`). The worktree config is re-read
/// for every file (a checkout or rebase can change it mid-command) and the
/// key reloaded when it changes.
pub(crate) struct Filters<'a> {
    root: &'a Path,
    current: Option<(Vec<u8>, Option<Key>)>,
    stored: Option<Option<Key>>,
}

impl<'a> Filters<'a> {
    pub(crate) fn new(root: &'a Path) -> Filters<'a> {
        Filters { root, current: None, stored: None }
    }

    /// One clean or smudge conversion of the file at `git_path`.
    pub(crate) fn convert(&mut self, clean: bool, git_path: &[u8], input: Zeroizing<Vec<u8>>)
        -> Result<Zeroizing<Vec<u8>>, String>
    {
        if transcrypt_v3_core::is_reserved_path(git_path) {
            return Err(format!("{} is selected for encryption, but v3 never encrypts .gitattributes, \
                .gitmodules or .transcrypt/; narrow the .gitattributes pattern that selects it",
                String::from_utf8_lossy(git_path)));
        }
        transcrypt_v3::validate_protected_path(git_path)?;
        let config = load_config(self.root)?;
        if self.current.as_ref().map(|(c, _)| c) != Some(&config) {
            let key = Key::load(self.root, &config)?;
            self.current = Some((config, key));
        }
        let Some((config, key)) = &self.current else { unreachable!() };
        let id = transcrypt_v3::config_id(config);
        let found = parse_file_header(&input).ok();
        if clean {
            // A record of another config (from before a rekey) cannot be
            // re-encrypted here. It passes through unchanged, so Git keeps
            // working, only if Git already has exactly these bytes at this
            // path (verification then refuses to commit it); anything else
            // starting with such a header is refused.
            if found.is_some_and(|found| found != id) {
                if blobs_at(self.root, git_path)?.contains(&blob_id(self.root, &input)?) { return Ok(input); }
                return Err(format!("{} starts like a record of another config but is not the one Git has \
                    for it; refusing to store it", String::from_utf8_lossy(git_path)));
            }
            let Some(key) = key else {
                // A worktree on another config than the stored key's (a branch
                // from before a rekey) shows files the stored key decrypted:
                // the record Git has for the path, if it opens to exactly
                // these bytes, is their clean form.
                if self.stored.is_none() { self.stored = Some(Key::stored(self.root)?); }
                if let Some(stored) = self.stored.as_ref().and_then(Option::as_ref) {
                    for oid in blobs_at(self.root, git_path)? {
                        let record = git_blob(self.root, &oid)?;
                        if parse_file_header(&record).is_ok_and(|f| f == stored.config_id())
                            && stored.open(git_path, &record).is_ok_and(|pt| *pt == *input) {
                            return Ok(Zeroizing::new(record));
                        }
                    }
                }
                // Locked: without the key nothing can be encrypted, but Git
                // re-cleans worktree files (a locked checkout holds
                // ciphertext), so a record of this configuration passes
                // through unchanged. Plaintext is refused, never stored.
                if record_envelope_ok(&input, &id) { return Ok(input); }
                return Err(Key::require(self.root, config).err().unwrap_or_default());
            };
            // `clean` returns a record that already opens at this path
            // unchanged and otherwise seals with the verified core's
            // `seal_record`, which refuses any other v3 record.
            let record = key.clean(git_path, &input)?;
            if key.private() && *record != *input {
                // Private mode: Git is staging plaintext of this file; if it
                // was created readable by others, make it private now.
                if let Some(target) = indexed_path(git_path).and_then(|p| find_protected(self.root, &p))? {
                    target.make_private()?;
                }
            }
            return Ok(record);
        }
        // The key for the config the record names: the worktree's, or the
        // stored key's own (Git may smudge files of a checkout before it
        // writes the new `.transcrypt/config`).
        if self.stored.is_none() { self.stored = Some(Key::stored(self.root)?); }
        let key = match found {
            Some(found) if found == id => key.as_ref(),
            Some(found) => self.stored.as_ref().and_then(Option::as_ref).filter(|k| k.config_id() == found),
            None => None,
        };
        let decided = key.map_or(id, Key::config_id);
        // The verified core decides: bytes that are no v3 record are refused,
        // a record without a key here stays encrypted, and a record of the
        // key's config is opened, which authenticates it at this exact path
        // or fails.
        match smudge_action(&input, &decided, key.is_some()) {
            Ok(SmudgeAction::Keep) => {
                if found.is_some_and(|found| found != id) && self.current.as_ref().is_some_and(|(_, k)| k.is_some()) {
                    eprintln!("transcrypt-v3: {} is encrypted under another config, without a key here; \
                        it stays encrypted (`transcrypt-v3 status` tells whether it needs `reencrypt`)",
                        String::from_utf8_lossy(git_path));
                }
                Ok(input)
            },
            Ok(SmudgeAction::Open) => {
                let Some(key) = key else { unreachable!() };
                let plaintext = key.open(git_path, &input).map_err(|_| {
                    let name = String::from_utf8_lossy(git_path);
                    format!("this record does not open at {name}: it was moved from another path or altered. \
                        If you moved it yourself (`git mv`), run `git add {name}` or commit, which re-encrypts \
                        it; if it came from a commit, that commit is broken or hostile")
                })?;
                if key.private() && !umask_is_private() {
                    // Git would create this file readable by other users:
                    // keep the (now authenticated) record; the post-checkout
                    // hook or `hydrate` publishes the plaintext with mode 0600.
                    return Ok(input);
                }
                Ok(plaintext)
            },
            Err(Refusal::Foreign) => Err("the committed file is not v3 ciphertext (it was stored without the \
                filter); refusing to present it as a protected file".into()),
            Err(_) => Err("input exceeds the 16 MiB v3 size limit".into()),
        }
    }
}

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

/// Whether files Git creates now are private to this user. Git creates
/// worktree files with mode `0666 & !umask`, and its filters inherit its
/// umask, so the smudge filter sees exactly the mask Git will apply.
pub(crate) fn umask_is_private() -> bool {
    // SAFETY: umask cannot fail; this process is single-threaded here and
    // restores the previous mask immediately.
    let previous = unsafe { libc::umask(0o077) };
    unsafe { libc::umask(previous) };
    previous & 0o077 == 0o077
}

/// Read-only summary for users. Never writes to the worktree, index or
/// credential directory.
fn status(root: &Path) -> Result<(), String> {
    let config = match load_config(root) {
        Ok(config) => config,
        Err(e) => {
            println!("repository: not initialized for v3 ({e})");
            return Ok(());
        }
    };
    println!("repository: v3 config {}", hex(&transcrypt_v3::config_id(&config)[..4]));
    let key = Key::load(root, &config)?;
    println!("key:        {}", match credential::state(root, &config)? {
        State::Unlocked { private: false } => "unlocked (stored in .git/transcrypt-v3/key)",
        State::Unlocked { private: true } => "unlocked (private: held in memory by an agent)",
        State::Locked => "locked",
        State::Stale => "locked: the stored key does not match .transcrypt/config (rekeyed?); run unlock",
    });
    let mut counts = [0usize; 4];
    let index = index_with_conflicts(root)?;
    for path in protected_paths(root, &index.conflicted)? {
        counts[2] += 1;
        println!("  {:<22} {}", "conflicted", String::from_utf8_lossy(&path));
    }
    let id = transcrypt_v3::config_id(&config);
    for staged in protected_entries(root, index.merged, Attributes::Staged)? {
        let name = String::from_utf8_lossy(&staged.path).into_owned();
        let state = (|| -> Result<&str, String> {
            if !staged.regular { return Ok("unsupported mode"); }
            let object = git_blob(root, &staged.oid)?;
            if !record_envelope_ok(&object, &id) {
                return Ok(if parse_file_header(&object).is_ok() { "other config (reencrypt)" } else { "staged unencrypted" });
            }
            let Some(target) = find_protected(root, &indexed_path(&staged.path)?)? else {
                return Ok("deleted");
            };
            let (worktree, _) = target.read()?;
            if *worktree == object { return Ok("ciphertext"); }
            let Some(key) = &key else { return Ok("modified or plaintext") };
            Ok(match key.open(&staged.path, &object) {
                Ok(plaintext) if *worktree == *plaintext => "plaintext",
                Ok(_) => "modified",
                Err(_) => "renamed or invalid",
            })
        })().unwrap_or("error");
        counts[match state { "ciphertext" => 0, "plaintext" => 1, "modified" | "modified or plaintext" | "deleted" => 2, _ => 3 }] += 1;
        println!("  {state:<22} {name}");
    }
    println!("protected:  {} ciphertext, {} plaintext, {} modified, {} other",
        counts[0], counts[1], counts[2], counts[3]);
    if counts[3] > 0 && key.is_some() {
        println!("note:       the pre-commit hook encrypts files you staged unencrypted and re-encrypts files you \
            renamed; files encrypted under an earlier config (cherry-picked or rebased across a rekey) need \
            `transcrypt-v3 reencrypt`");
    }
    let untracked = git(root, &["ls-files", "--others", "--exclude-standard", "-z"])?;
    let untracked: Vec<&[u8]> = untracked.split(|b| *b == 0).filter(|p| !p.is_empty()).collect();
    let loose = protected_flags(root, &untracked, Attributes::Worktree)?.into_iter().filter(|p| *p).count();
    if loose > 0 {
        println!("note:       {loose} untracked protected file(s); `git add` encrypts them");
    }
    if key.is_some() && counts[0] > 0 {
        println!("hint:       run `transcrypt-v3 hydrate` to decrypt ciphertext in the worktree");
    }
    if hooks_bypassed(root) {
        println!("warning:    {HOOKS_BYPASSED}");
    }
    Ok(())
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn config_path(root: &Path) -> Result<PathBuf, String> {
    let dir = root.join(".transcrypt");
    let meta = fs::symlink_metadata(&dir).map_err(|_| "missing .transcrypt directory: run init or clone a v3 repository")?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err("unsafe .transcrypt directory".into());
    }
    let file = dir.join("config");
    let fmeta = fs::symlink_metadata(&file).map_err(|_| "missing committed .transcrypt/config")?;
    if !fmeta.is_file() || fmeta.file_type().is_symlink() {
        return Err("unsafe .transcrypt/config type".into());
    }
    Ok(file)
}

pub(crate) fn load_config(root: &Path) -> Result<Vec<u8>, String> {
    let bytes = fs::read(config_path(root)?).map_err(|e| format!("cannot read v3 config: {e}"))?;
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
    Ok(bytes)
}
