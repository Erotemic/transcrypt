//! The command line: each command with exactly the arguments it takes
//! (`Command`, and `AuditArgs`), parsed from the raw arguments, and the
//! usage and help texts. Parsing does nothing else; `main.rs` runs them.
//! `help` and `version` take nothing and are answered by `main.rs` first.

use std::{ffi::OsString, time::Duration};

/// A command that works in a worktree's repository, with its arguments.
pub(crate) enum Command {
    Status,
    Doctor,
    /// Git's long-running filter process.
    FilterProcess,
    Lock,
    /// `lock` of one worktree, run by `lock` in each of the others.
    Flush,
    /// Whether this worktree holds no plaintext, run by `lock` and
    /// `uninstall` in each other worktree.
    CheckEncrypted,
    VerifyIndex,
    PreCommit,
    /// The private mode's credential agent, started by `unlock --private`.
    Serve,
    Uninstall,
    /// `hydrate`; with `auto`, run from Git's hooks (`hydrate --auto`).
    Hydrate { auto: bool },
    Init(InitArgs),
    Unlock(UnlockArgs),
    Rekey { password_stdin: bool },
    Migrate(MigrateArgs),
    Reencrypt(ReencryptArgs),
    /// `.gitattributes` patterns, at least one.
    Protect(Vec<OsString>),
    Unprotect(Vec<OsString>),
    /// Git's external diff of a protected file.
    Diff(DiffArgs),
    /// Git's external diff of an unmerged path, which has no sides.
    DiffUnmerged { path: OsString },
    /// Git's merge driver (`%O %A %B %P`).
    Merge(MergeArgs),
    /// Git's clean (`clean`) or smudge filter of the file at `path` (`%f`).
    Filter { clean: bool, path: OsString },
    /// The pre-push hook: Git passes the remote's name (and URL).
    PrePush { remote: Option<OsString> },
}

/// Where an unlocked key is kept.
#[derive(Clone, Copy)]
pub(crate) enum KeyMode {
    /// Stored in `.git/transcrypt-v3/key` (the default).
    Stored,
    /// `--private`: held in memory by the credential agent, which forgets it
    /// after `idle` without use (`--timeout`), with decrypted files private.
    Private { idle: Option<Duration> },
}

impl KeyMode {
    pub(crate) fn private(self) -> bool {
        matches!(self, KeyMode::Private { .. })
    }
}

/// `init [--password-stdin] [--private [--timeout=DURATION]] [PATTERN...]`.
pub(crate) struct InitArgs {
    pub(crate) password_stdin: bool,
    pub(crate) mode: KeyMode,
    pub(crate) patterns: Vec<OsString>,
}

/// `unlock [--password-stdin] [--private [--timeout=DURATION]] [--no-hydrate]`.
pub(crate) struct UnlockArgs {
    pub(crate) password_stdin: bool,
    pub(crate) mode: KeyMode,
    /// Decrypt the worktree once unlocked (not with `--no-hydrate`).
    pub(crate) hydrate: bool,
}

/// `migrate [--password-stdin] [--private]`.
pub(crate) struct MigrateArgs {
    pub(crate) password_stdin: bool,
    pub(crate) mode: KeyMode,
}

/// `reencrypt [--password-stdin] [--yes]`.
pub(crate) struct ReencryptArgs {
    pub(crate) password_stdin: bool,
    /// The user already reviewed what will be trusted.
    pub(crate) yes: bool,
}

/// Git's external diff interface for one file: its old and new sides, each
/// a file Git wrote and the Git path it is at.
pub(crate) struct DiffArgs {
    pub(crate) old_path: OsString,
    pub(crate) old: OsString,
    pub(crate) new_path: OsString,
    pub(crate) new: OsString,
}

/// Git's merge driver arguments: the base, ours (where the result goes) and
/// theirs, and the Git path being merged.
pub(crate) struct MergeArgs {
    pub(crate) base: OsString,
    pub(crate) ours: OsString,
    pub(crate) theirs: OsString,
    pub(crate) path: OsString,
}

/// `audit [--max-commits=N] [<rev-list args>]`, which (unlike a `Command`)
/// also runs in a bare repository.
pub(crate) struct AuditArgs {
    pub(crate) max_commits: Option<usize>,
    pub(crate) revs: Vec<OsString>,
}

impl Command {
    /// The command `action` with the arguments that follow it, `args`.
    pub(crate) fn parse(action: &str, args: &[OsString]) -> Result<Command, String> {
        Ok(match action {
            "status" | "doctor" | "filter-process" | "lock" | "flush" | "check-encrypted" | "verify-index"
                | "pre-commit" | "serve" | "uninstall" if !args.is_empty() => return Err(format!("{action} takes no arguments")),
            "status" => Command::Status,
            "doctor" => Command::Doctor,
            "filter-process" => Command::FilterProcess,
            "lock" => Command::Lock,
            "flush" => Command::Flush,
            "check-encrypted" => Command::CheckEncrypted,
            "verify-index" => Command::VerifyIndex,
            "pre-commit" => Command::PreCommit,
            "serve" => Command::Serve,
            "uninstall" => Command::Uninstall,
            "hydrate" => match args {
                [] => Command::Hydrate { auto: false },
                [flag] if flag == "--auto" => Command::Hydrate { auto: true },
                _ => return Err("hydrate takes no arguments".into()),
            },
            "init" | "unlock" | "rekey" | "migrate" | "reencrypt" => parse_passphrase_command(action, args)?,
            "protect" | "unprotect" if args.is_empty() => {
                return Err(format!("{action} takes one or more .gitattributes patterns"));
            },
            "protect" => Command::Protect(args.to_vec()),
            "unprotect" => Command::Unprotect(args.to_vec()),
            // Git's external diff interface: path old-file old-hex old-mode
            // new-file new-hex new-mode [new-path rename-message].
            "diff" => match args {
                [path, old, _, _, new, _, _] => Command::Diff(DiffArgs {
                    old_path: path.clone(), old: old.clone(), new_path: path.clone(), new: new.clone(),
                }),
                [path, old, _, _, new, _, _, new_path, _] => Command::Diff(DiffArgs {
                    old_path: path.clone(), old: old.clone(), new_path: new_path.clone(), new: new.clone(),
                }),
                [path] => Command::DiffUnmerged { path: path.clone() },
                _ => return Err("unexpected external diff arguments".into()),
            },
            "merge" => match args {
                [base, ours, theirs, path] => Command::Merge(MergeArgs {
                    base: base.clone(), ours: ours.clone(), theirs: theirs.clone(), path: path.clone(),
                }),
                _ => return Err("merge driver takes %O %A %B %P".into()),
            },
            "clean" | "smudge" => match args {
                [path] => Command::Filter { clean: action == "clean", path: path.clone() },
                _ => return Err("Git filter requires exactly one %f pathname".into()),
            },
            "pre-push" if args.len() > PRE_PUSH_ARGUMENTS => return Err("pre-push takes the remote name and URL".into()),
            "pre-push" => Command::PrePush { remote: args.first().cloned() },
            _ => return Err(format!("unknown v3 operation; {USAGE}")),
        })
    }
}

/// Git passes the pre-push hook the remote's name and URL.
const PRE_PUSH_ARGUMENTS: usize = 2;

/// `init`, `unlock`, `rekey`, `migrate` or `reencrypt` (`action`): each
/// argument in order, refused unless `action` takes it.
fn parse_passphrase_command(action: &str, args: &[OsString]) -> Result<Command, String> {
    let (mut password_stdin, mut private, mut hydrate, mut yes) = (false, false, true, false);
    let mut idle = None;
    let mut patterns = Vec::new();
    for arg in args {
        let flag = arg.to_str();
        if let (Some(duration), "init" | "unlock") = (flag.and_then(|f| f.strip_prefix("--timeout=")), action) {
            idle = Some(parse_duration(duration)?);
            continue;
        }
        match (flag, action) {
            (Some("--password-stdin"), _) => password_stdin = true,
            (Some("--private"), "init" | "unlock" | "migrate") => private = true,
            (Some("--no-hydrate"), "unlock") => hydrate = false,
            (Some("--yes"), "reencrypt") => yes = true,
            (Some(flag), _) if flag.starts_with('-') => return Err(format!("{action}: unknown option {flag}")),
            (_, "init") => patterns.push(arg.clone()),
            _ => return Err(format!("{action}: unexpected argument {}", arg.to_string_lossy())),
        }
    }
    let mode = match (private, idle) {
        (true, idle) => KeyMode::Private { idle },
        (false, None) => KeyMode::Stored,
        (false, Some(_)) => return Err("--timeout applies to the private mode: use it with --private".into()),
    };
    Ok(match action {
        "init" => Command::Init(InitArgs { password_stdin, mode, patterns }),
        "unlock" => Command::Unlock(UnlockArgs { password_stdin, mode, hydrate }),
        "rekey" => Command::Rekey { password_stdin },
        "migrate" => Command::Migrate(MigrateArgs { password_stdin, mode }),
        _ => Command::Reencrypt(ReencryptArgs { password_stdin, yes }),
    })
}

impl AuditArgs {
    /// `audit`'s arguments: an optional first `--max-commits=N`, then what
    /// `git rev-list` takes.
    pub(crate) fn parse(args: &[OsString]) -> Result<AuditArgs, String> {
        let limit = args.first().and_then(|a| a.to_str()).and_then(|a| a.strip_prefix("--max-commits="));
        Ok(match limit {
            Some(limit) => AuditArgs {
                max_commits: Some(limit.parse::<usize>().map_err(|_| "--max-commits takes a number")?),
                revs: args[1..].to_vec(),
            },
            None => AuditArgs { max_commits: None, revs: args.to_vec() },
        })
    }
}

pub(crate) const USAGE: &str ="usage: transcrypt-rs init|protect|unprotect|unlock|status|doctor|lock|rekey|hydrate|\
    verify-index|audit|migrate|uninstall|help|version (clean, smudge, filter-process, diff, merge, pre-commit and \
    pre-push are invoked by Git)";

pub(crate) const HELP: &str = "\
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

/// Seconds in each unit `parse_duration` accepts.
const SECOND: u64 = 1;
const MINUTE: u64 = 60 * SECOND;
const HOUR: u64 = 60 * MINUTE;

/// A positive duration: a number with an optional unit `s`, `m` (the
/// default) or `h`.
fn parse_duration(text: &str) -> Result<Duration, String> {
    let (number, unit) = match text.char_indices().find(|(_, c)| !c.is_ascii_digit()) {
        Some((i, _)) => text.split_at(i),
        None => (text, "m"),
    };
    let scale = match unit { "s" => Some(SECOND), "m" => Some(MINUTE), "h" => Some(HOUR), _ => None };
    match (number.parse::<u64>(), scale) {
        (Ok(n), Some(scale)) if n > 0 => Ok(Duration::from_secs(n.saturating_mul(scale))),
        _ => Err(format!("--timeout takes a positive duration such as 90s, 15m or 2h (got {text:?})")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Command::parse` of a command line whose words are separated by spaces.
    fn parse(line: &str) -> Result<Command, String> {
        let mut words = line.split(' ');
        let action = words.next().unwrap_or_default();
        Command::parse(action, &words.map(OsString::from).collect::<Vec<_>>())
    }

    /// Each command takes exactly its own options, in any order, and says
    /// which argument it refuses.
    #[test]
    fn commands_take_only_their_own_arguments() {
        let ninety_seconds = Some(Duration::from_secs(90 * SECOND));
        match parse("init --private a.env --timeout=90s --password-stdin b/**") {
            Ok(Command::Init(InitArgs { password_stdin: true, mode: KeyMode::Private { idle }, patterns })) =>
                assert!(idle == ninety_seconds && patterns == ["a.env", "b/**"]),
            _ => panic!("init"),
        }
        assert!(matches!(parse("unlock --no-hydrate"),
            Ok(Command::Unlock(UnlockArgs { password_stdin: false, mode: KeyMode::Stored, hydrate: false }))));
        assert!(matches!(parse("migrate --private"),
            Ok(Command::Migrate(MigrateArgs { mode: KeyMode::Private { idle: None }, .. }))));
        assert!(matches!(parse("reencrypt --yes"), Ok(Command::Reencrypt(ReencryptArgs { yes: true, .. }))));
        assert!(matches!(parse("rekey --password-stdin"), Ok(Command::Rekey { password_stdin: true })));
        assert!(matches!(parse("hydrate --auto"), Ok(Command::Hydrate { auto: true })));
        assert!(matches!(parse("pre-push origin url"), Ok(Command::PrePush { remote: Some(_) })));
        assert!(matches!(parse("diff a.env old 1 100644 new 2 100644 b.env renamed"),
            Ok(Command::Diff(DiffArgs { old_path, new_path, .. })) if old_path == "a.env" && new_path == "b.env"));
        for (line, refusal) in [
            ("unlock --timeout=90s", "--timeout applies to the private mode: use it with --private"),
            ("migrate --timeout=90s", "migrate: unknown option --timeout=90s"),
            ("rekey --private", "rekey: unknown option --private"),
            ("unlock a.env", "unlock: unexpected argument a.env"),
            ("reencrypt --no-hydrate", "reencrypt: unknown option --no-hydrate"),
            ("status now", "status takes no arguments"),
            ("hydrate --all", "hydrate takes no arguments"),
            ("protect", "protect takes one or more .gitattributes patterns"),
            ("diff a.env old", "unexpected external diff arguments"),
            ("merge a b c", "merge driver takes %O %A %B %P"),
            ("clean", "Git filter requires exactly one %f pathname"),
            ("pre-push a b c", "pre-push takes the remote name and URL"),
        ] {
            assert_eq!(parse(line).err().as_deref(), Some(refusal), "{line}");
        }
        assert!(parse("unlock --private --timeout=0").is_err_and(|e| e.starts_with("--timeout takes a positive duration")));
        assert!(parse("frobnicate").is_err_and(|e| e.starts_with("unknown v3 operation; usage:")));
    }

    #[test]
    fn audit_takes_an_optional_first_commit_limit() {
        let audit = |args: &[&str]| AuditArgs::parse(&args.iter().map(OsString::from).collect::<Vec<_>>());
        let limited = audit(&["--max-commits=7", "HEAD"]).unwrap();
        assert!(limited.max_commits == Some(7) && limited.revs == ["HEAD"]);
        assert!(audit(&["HEAD", "--max-commits=7"]).unwrap().max_commits.is_none());
        assert_eq!(audit(&["--max-commits=x"]).err().as_deref(), Some("--max-commits takes a number"));
    }
}
