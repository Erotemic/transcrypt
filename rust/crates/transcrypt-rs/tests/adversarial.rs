//! Adversarial and fault-recovery lifecycle tests (roadmap stage V5) against
//! real Git repositories and the real credential agent.
mod common;
use common::*;
use std::io::{Read, Write};
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::{fs, time::Duration};

#[test]
fn interrupted_lock_resumes_and_unstaged_edits_are_never_discarded() {
    let mut scratch = Scratch::new("lock");
    let repo = scratch.repo("repo");
    let a_record = staged(&repo, "a.secret");
    // Crash after flushing a.secret but before dir/b.secret: rerun completes.
    fs::write(repo.join("a.secret"), &a_record).unwrap();
    run(&repo, bin(), &["lock"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), a_record);
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), staged(&repo, "dir/b.secret"));
    assert!(!unlocked(&repo));

    unlock(&repo);
    run(&repo, bin(), &["hydrate"], None);
    // An unstaged edit is the user's only copy: lock must refuse and keep it.
    fs::write(repo.join("dir/b.secret"), b"unsaved edit\n").unwrap();
    run_fails(&repo, bin(), &["lock"], None);
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), b"unsaved edit\n");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert!(unlocked(&repo), "a refused lock keeps the key available");
    fs::write(repo.join("dir/b.secret"), b"beta plaintext\n").unwrap();
    run(&repo, bin(), &["lock"], None);
}

#[test]
fn crash_leftovers_never_reach_the_worktree_and_are_purged() {
    let mut scratch = Scratch::new("staging");
    let repo = scratch.repo("repo");
    fs::write(repo.join("a.secret"), staged(&repo, "a.secret")).unwrap();
    // Simulate a hydrate that crashed after writing a private temporary.
    let staging = repo.join(".git/transcrypt-v3-staging");
    fs::create_dir_all(&staging).unwrap();
    make_private_dir(&staging);
    fs::write(staging.join("12345-0.tmp"), b"alpha plaintext\n").unwrap();
    assert!(run(&repo, "git", &["status", "--porcelain", "--untracked-files=all"], None)
        .split(|b| *b == b'\n').all(|l| !l.ends_with(b".tmp")));
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert_eq!(fs::read_dir(&staging).unwrap().count(), 0, "stale plaintext purged");
    // No temporary ever appears next to protected files.
    for dir in [repo.clone(), repo.join("dir")] {
        for entry in fs::read_dir(dir).unwrap() {
            let name = entry.unwrap().file_name();
            assert!(!name.to_string_lossy().contains("transcrypt-v3"), "worktree temp {name:?}");
        }
    }
    // A hostile symlink in place of the staging directory is refused.
    fs::remove_dir_all(&staging).unwrap();
    symlink(&repo.join("dir"), &staging);
    fs::write(repo.join("a.secret"), staged(&repo, "a.secret")).unwrap();
    run_fails(&repo, bin(), &["hydrate"], None);
    remove_link(&staging);
}

#[test]
fn symlinked_protected_files_are_never_followed() {
    let mut scratch = Scratch::new("symlink");
    let repo = scratch.repo("repo");
    let outside = scratch.root.join("outside.secret");
    let record = staged(&repo, "a.secret");
    fs::write(&outside, &record).unwrap();
    fs::remove_file(repo.join("a.secret")).unwrap();
    symlink(&outside, &repo.join("a.secret"));
    run_fails(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(&outside).unwrap(), record, "hydrate must not write through a symlink");
    // Lock first verifies the index; it must also refuse to follow the link.
    run_fails(&repo, bin(), &["lock"], None);
    assert_eq!(fs::read(&outside).unwrap(), record);
    fs::remove_file(repo.join("a.secret")).unwrap();
    fs::write(repo.join("a.secret"), b"alpha plaintext\n").unwrap();
}

#[test]
fn stale_agent_socket_is_reclaimed_but_live_agent_is_not_replaced() {
    let mut scratch = Scratch::new("socket");
    let repo = scratch.repo("repo");
    private(&repo);
    // Unlocking again keeps the live agent (and needs no passphrase).
    let out = exec(&repo, bin(), &["unlock", "--private"], None);
    assert!(out.status.success() && String::from_utf8_lossy(&out.stderr).contains("Already unlocked"));
    run(&repo, bin(), &["lock"], None);
    // A dead agent leaves its socket inode behind; it has no listener.
    drop(UnixListener::bind(socket(&repo)).unwrap());
    assert!(socket(&repo).exists());
    run(&repo, bin(), &["unlock", "--private", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["verify-index"], None);
    // A regular file squatting on the socket path is never removed.
    run(&repo, bin(), &["lock"], None);
    fs::write(socket(&repo), b"not a socket").unwrap();
    run_fails(&repo, bin(), &["unlock", "--private", "--password-stdin"], Some(PASS));
    fs::remove_file(socket(&repo)).unwrap();
}

#[test]
fn agent_refuses_hostile_requests_and_keeps_serving() {
    let mut scratch = Scratch::new("agent");
    let repo = scratch.repo("repo");
    private(&repo);
    let config = fs::read(repo.join(".transcrypt/config")).unwrap();
    let record = staged(&repo, "a.secret");
    assert_eq!(agent_request(&repo, b'D', &config, b"a.secret", &record).unwrap(), b"alpha plaintext\n");
    let mut foreign = config.clone();
    foreign[20] ^= 1;
    for (op, cfg, path, body) in [
        (b'D', &foreign, &b"a.secret"[..], &record[..]),   // different public config
        (b'D', &config, b"dir/b.secret", &record[..]),     // cross-path replay
        (b'D', &config, b"../a.secret", &record[..]),      // noncanonical path
        (b'D', &config, b"a.txt", &record[..]),            // another path
        (b'D', &config, b".gitattributes", &record[..]),   // reserved path
        (b'E', &config, b"dir/b.secret", &record[..]),     // double encryption
        (b'P', &config, b"a.secret", &b""[..]),            // control op with a path
        (b'Q', &config, b"", &b""[..]),                    // unknown opcode
    ] {
        assert!(agent_request(&repo, op, cfg, path, body).is_err(), "accepted op {}", op as char);
    }
    // Clean is idempotent: an authentic record at its own path is returned.
    assert_eq!(agent_request(&repo, b'E', &config, b"a.secret", &record).unwrap(), record);
    // A truncated frame must not take the agent down.
    drop(UnixStream::connect(socket(&repo)).unwrap().write_all(b"D"));
    assert!(agent_request(&repo, b'P', &config, b"", b"").is_ok(), "agent survives hostile clients");
}

#[test]
fn foreign_truncated_and_plaintext_index_entries_fail_closed() {
    let mut scratch = Scratch::new("index");
    let repo = scratch.repo("repo");
    let other = scratch.repo("other");
    // Valid ciphertext from another repository (different salt and key).
    let foreign = staged(&other, "a.secret");
    let id = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"], Some(&foreign))).unwrap();
    run(&repo, "git", &["update-index", "--cacheinfo", "100644", id.trim(), "a.secret"], None);
    run_fails(&repo, bin(), &["verify-index"], None);
    run(&repo, "git", &["reset", "-q", "HEAD", "--", "a.secret"], None);
    run(&repo, bin(), &["verify-index"], None);
    // Truncated record (tag cut short) and an appended byte.
    let record = staged(&repo, "dir/b.secret");
    for bad in [record[..record.len() - 1].to_vec(), [record.clone(), vec![0]].concat()] {
        let id = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"], Some(&bad))).unwrap();
        run(&repo, "git", &["update-index", "--cacheinfo", "100644", id.trim(), "dir/b.secret"], None);
        run_fails(&repo, bin(), &["verify-index"], None);
        run_fails(&repo, bin(), &["hydrate"], None);
        run(&repo, "git", &["reset", "-q", "HEAD", "--", "dir/b.secret"], None);
    }
    // Committing a record copied from another path is refused by clean.
    fs::write(repo.join("copy.secret"), staged(&repo, "a.secret")).unwrap();
    run_fails(&repo, "git", &["add", "copy.secret"], None);
    fs::remove_file(repo.join("copy.secret")).unwrap();
    run(&repo, bin(), &["verify-index"], None);
}

#[test]
fn help_and_status_report_state_without_changing_anything() {
    let mut scratch = Scratch::new("status");
    let help = String::from_utf8(run(&scratch.root, bin(), &["help"], None)).unwrap();
    assert!(help.contains("transcrypt-rs unlock") && help.contains("transcrypt-rs protect PATTERN"));
    let version = String::from_utf8(run(&scratch.root, bin(), &["--version"], None)).unwrap();
    assert!(version.starts_with(&format!("transcrypt-rs {}", env!("CARGO_PKG_VERSION"))), "{version}");
    let repo = scratch.repo("repo");
    let text = |repo: &Path| String::from_utf8(run(repo, bin(), &["status"], None)).unwrap();
    let unlocked = text(&repo);
    assert!(unlocked.contains("key:        unlocked (stored"), "{unlocked}");
    assert!(unlocked.contains("2 plaintext"), "{unlocked}");
    fs::write(repo.join("a.secret"), b"edited\n").unwrap();
    fs::write(repo.join("new.secret"), b"untracked\n").unwrap();
    let edited = text(&repo);
    assert!(edited.contains("modified") && edited.contains("1 untracked protected"), "{edited}");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"edited\n", "status is read-only");
    fs::remove_file(repo.join("new.secret")).unwrap();
    fs::write(repo.join("a.secret"), b"alpha plaintext\n").unwrap();
    run(&repo, bin(), &["lock"], None);
    let locked = text(&repo);
    assert!(locked.contains("key:        locked") && locked.contains("2 ciphertext"), "{locked}");
}

#[cfg(target_os = "linux")]
#[test]
fn key_agent_is_not_dumpable_or_ptrace_readable() {
    use std::os::fd::AsRawFd;
    let mut scratch = Scratch::new("dump");
    let repo = scratch.repo("repo");
    private(&repo);
    let stream = UnixStream::connect(socket(&repo)).unwrap();
    let mut cred = libc::ucred { pid: 0, uid: 0, gid: 0 };
    let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    // SAFETY: getsockopt writes at most `len` bytes into `cred`.
    let rc = unsafe {
        libc::getsockopt(stream.as_raw_fd(), libc::SOL_SOCKET, libc::SO_PEERCRED,
            (&mut cred as *mut libc::ucred).cast(), &mut len)
    };
    assert_eq!(rc, 0);
    drop(stream);
    let proc_dir = PathBuf::from(format!("/proc/{}", cred.pid));
    let limits = fs::read_to_string(proc_dir.join("limits")).unwrap();
    let core = limits.lines().find(|l| l.starts_with("Max core file size")).unwrap();
    assert!(core.split_whitespace().nth(4) == Some("0"), "core dumps enabled: {core}");
    // The kernel makes a non-dumpable process's /proc entries root-owned,
    // which is what denies same-UID ptrace attach and /proc/PID/mem reads.
    use std::os::unix::fs::MetadataExt;
    let owner = fs::metadata(proc_dir.join("environ")).unwrap().uid();
    assert_eq!(owner, 0, "agent is dumpable: /proc entries owned by uid {owner}");
}

#[test]
fn deep_repository_paths_and_subdirectories_work() {
    let mut scratch = Scratch::new("deep");
    // The absolute socket path would exceed the 104/108-byte sun_path limit.
    let deep = scratch.root.join("a".repeat(60)).join("b".repeat(60));
    fs::create_dir_all(&deep).unwrap();
    let repo_name = deep.strip_prefix(&scratch.root).unwrap().join("repo");
    let repo = scratch.repo(repo_name.to_str().unwrap());
    assert!(socket(&repo).as_os_str().len() > 108);
    run(&repo.join("dir"), bin(), &["status"], None);
    run(&repo.join("dir"), bin(), &["verify-index"], None);
    run(&repo, bin(), &["lock"], None);
    run(&repo.join("dir"), bin(), &["unlock", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), b"beta plaintext\n");
}

#[test]
fn failed_init_rolls_back_so_it_can_be_rerun() {
    let scratch = Scratch::new("rollback");
    let repo = scratch.root.join("repo");
    fs::create_dir(&repo).unwrap();
    run(&repo, "git", &["init", "-q"], None);
    // A regular file squatting on the socket path makes agent startup fail.
    let dir = repo.join(".git/transcrypt-v3");
    fs::create_dir(&dir).unwrap();
    make_private_dir(&dir);
    fs::write(dir.join("session.sock"), b"squatter").unwrap();
    let err = run_fails(&repo, bin(), &["init", "--private", "--password-stdin"], Some(PASS));
    assert!(err.contains("rolled back"), "{err}");
    assert!(!repo.join(".transcrypt").exists());
    assert!(!repo.join(".gitattributes").exists());
    assert!(!repo.join(".git/hooks/pre-commit").exists());
    assert!(exec(&repo, "git", &["config", "--local", "--get", "filter.transcrypt-v3.clean"], None)
        .stdout.is_empty());
    assert!(run(&repo, "git", &["diff", "--cached", "--name-only"], None).is_empty());
    fs::remove_file(dir.join("session.sock")).unwrap();
    run(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["lock"], None);
}

#[test]
fn unlock_hydrates_by_default_and_reports_refusals() {
    let mut scratch = Scratch::new("autohydrate");
    let repo = scratch.repo("repo");
    run(&repo, bin(), &["lock"], None);
    let clone = scratch.clone("repo", "clone");
    unlock(&clone);
    assert_eq!(fs::read(clone.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert_eq!(fs::read(clone.join("dir/b.secret")).unwrap(), b"beta plaintext\n");
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    run(&clone, bin(), &["lock"], None);
    // A local edit made while locked survives unlock untouched (and stays
    // unstaged); every other file is decrypted.
    fs::write(clone.join("dir/b.secret"), b"local edit\n").unwrap();
    unlock(&clone);
    assert_eq!(fs::read(clone.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert_eq!(fs::read(clone.join("dir/b.secret")).unwrap(), b"local edit\n");
    let status = run(&clone, "git", &["status", "--porcelain"], None);
    assert_eq!(status, b" M dir/b.secret\n", "{}", String::from_utf8_lossy(&status));
    fs::write(clone.join("dir/b.secret"), b"beta plaintext\n").unwrap();
    run(&clone, bin(), &["lock"], None);
    // A refusal (a protected file replaced by a symlink) leaves everything
    // unchanged, and unlock still succeeds and says so.
    let record = fs::read(clone.join("a.secret")).unwrap();
    fs::remove_file(clone.join("dir/b.secret")).unwrap();
    symlink(Path::new("../a.secret"), &clone.join("dir/b.secret"));
    let out = exec(&clone, bin(), &["unlock", "--password-stdin"], Some(PASS));
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("decryption changed nothing"));
    assert_eq!(fs::read(clone.join("a.secret")).unwrap(), record);
    fs::remove_file(clone.join("dir/b.secret")).unwrap();
    run(&clone, "git", &["checkout", "--", "dir/b.secret"], None);
}

/// Regression: hydration refreshed the index with `git add -- <path>`, which
/// Git reads as a pathspec. A hostile commit adding `sub/[a].secret` (a glob
/// matching `sub/a.secret`) next to `sub/.gitattributes: a.secret -filter`
/// made `unlock` stage an untracked plaintext `sub/a.secret` unencrypted.
#[test]
fn hydration_never_stages_untracked_files_through_pathspec_magic() {
    let mut scratch = Scratch::new("pathspec");
    let repo = scratch.repo("repo");
    fs::create_dir(repo.join("sub")).unwrap();
    fs::write(repo.join("sub/.gitattributes"), b"a.secret -filter\n").unwrap();
    fs::write(repo.join("sub/[a].secret"), b"decoy\n").unwrap();
    // Windows file names cannot contain `:` or `*`.
    let magic = cfg!(unix);
    if magic { fs::write(repo.join("sub/:(glob)*.secret"), b"decoy two\n").unwrap(); }
    commit(&repo, &["sub"], "hostile names");
    run(&repo, bin(), &["lock"], None);
    fs::write(repo.join("sub/a.secret"), b"UNTRACKED PLAINTEXT\n").unwrap();
    fs::write(repo.join("sub/b.secret"), b"UNTRACKED PLAINTEXT\n").unwrap();
    unlock(&repo);
    let staged = run(&repo, "git", &["ls-files", "-z", "sub"], None);
    let expected: &[u8] = if magic { b"sub/.gitattributes\0sub/:(glob)*.secret\0sub/[a].secret\0" }
        else { b"sub/.gitattributes\0sub/[a].secret\0" };
    assert_eq!(staged, expected, "untracked file staged");
    assert_eq!(fs::read(repo.join("sub/[a].secret")).unwrap(), b"decoy\n");
    if magic { assert_eq!(fs::read(repo.join("sub/:(glob)*.secret")).unwrap(), b"decoy two\n"); }
    let status = run(&repo, "git", &["status", "--porcelain", "--untracked-files=no"], None);
    assert!(status.is_empty(), "{}", String::from_utf8_lossy(&status));
    fs::remove_file(repo.join("sub/a.secret")).unwrap();
    fs::remove_file(repo.join("sub/b.secret")).unwrap();
}

/// Regression: staged objects were read with `git show :<path>`, so a
/// protected file named `0:a.secret` was read as stage 0 of `a.secret`.
/// Objects are now read by the object id of the verified index snapshot.
#[test]
#[cfg(unix)] // Windows file names cannot contain `:`, so none looks like `0:path`.
fn staged_objects_are_read_by_object_id_not_revision_syntax() {
    let mut scratch = Scratch::new("revsyntax");
    let repo = scratch.repo("repo");
    fs::write(repo.join("0:a.secret"), b"colon plaintext\n").unwrap();
    commit(&repo, &["0:a.secret"], "colon name");
    run(&repo, bin(), &["verify-index"], None);
    run(&repo, bin(), &["lock"], None);
    unlock(&repo);
    assert_eq!(fs::read(repo.join("0:a.secret")).unwrap(), b"colon plaintext\n");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
}

/// Plaintext that reaches a commit without passing the pre-commit hook
/// (`--no-verify`, a filter disabled when the file was added, or a clone
/// that never ran unlock) is refused by the pre-push hook and by `audit`,
/// which needs no key.
#[test]
fn pre_push_and_audit_refuse_plaintext_in_history() {
    let mut scratch = Scratch::new("audit");
    let repo = scratch.repo("repo");
    run(&scratch.root, "git", &["init", "-q", "--bare", "remote.git"], None);
    run(&repo, "git", &["remote", "add", "origin", "../remote.git"], None);
    run(&repo, "git", &["push", "-q", "origin", "HEAD:refs/heads/main"], None);
    let out = String::from_utf8(run(&repo, bin(), &["audit"], None)).unwrap();
    assert!(out.contains("2 protected record(s) checked, all authenticated"), "{out}");
    // A plaintext secret committed with --no-verify.
    let blob = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"],
        Some(b"PLAINTEXT LEAK\n"))).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", "100644", blob.trim(), "leak.secret"], None);
    // The pre-commit hook encrypts what was staged around the filter.
    run(&repo, "git", &["commit", "-qm", "sealed by pre-commit"], None);
    assert!(is_record(&staged(&repo, "leak.secret")));
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", "100644", blob.trim(), "leak.secret"], None);
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "bypass"], None);
    let err = run_fails(&repo, "git", &["push", "-q", "origin", "HEAD:refs/heads/main"], None);
    assert!(err.contains("leak.secret") && err.contains("refusing to push"), "{err}");
    run_fails(&repo, bin(), &["audit"], None);
    // The keyless audit refuses it too, and accepts the earlier history.
    run(&repo, "git", &["branch", "leaky"], None);
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    // A bare server repository (as in a pre-receive hook) audits keylessly.
    let remote = scratch.root.join("remote.git");
    let out = String::from_utf8(run(&remote, bin(), &["audit", "--all"], None)).unwrap();
    assert!(out.contains("2 protected record(s) checked (envelopes only"), "{out}");
    run(&repo, "git", &["push", "-q", "--no-verify", "origin", "leaky:refs/heads/leaky"], None);
    let err = run_fails(&remote, bin(), &["audit", "--all"], None);
    assert!(err.contains("leak.secret"), "{err}");
    run(&repo, "git", &["push", "-q", "origin", ":refs/heads/leaky"], None);
    run(&repo, bin(), &["lock"], None);
    run_fails(&repo, bin(), &["audit", "leaky"], None);
    let out = String::from_utf8(run(&repo, bin(), &["audit", "HEAD"], None)).unwrap();
    assert!(out.contains("envelopes only"), "{out}");
    // A clone that never ran unlock has no filter: a new secret is committed
    // as plaintext. Its own audit (as CI or a server hook would run) refuses.
    let clone = scratch.root.join("clone");
    run(&scratch.root, "git", &["clone", "-q", "-b", "main", "remote.git", "clone"], None);
    Scratch::identify(&clone);
    fs::write(clone.join("new.secret"), b"FRESH CLONE PLAINTEXT\n").unwrap();
    commit(&clone, &["new.secret"], "unfiltered");
    let err = run_fails(&clone, bin(), &["audit", "origin/main..HEAD"], None);
    assert!(err.contains("new.secret"), "{err}");
    run(&clone, bin(), &["audit", "origin/main"], None);
}

/// While locked, the pre-commit hook still refuses staged plaintext (by its
/// envelope), but commits of unrelated files keep working.
#[test]
fn locked_pre_commit_checks_envelopes_and_allows_other_commits() {
    let mut scratch = Scratch::new("lockedhook");
    let repo = scratch.repo("repo");
    run(&repo, bin(), &["lock"], None);
    fs::write(repo.join("README"), b"public edit\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "public change while locked"], None);
    let blob = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"],
        Some(b"PLAINTEXT WHILE LOCKED\n"))).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", "100644", blob.trim(), "late.secret"], None);
    run_fails(&repo, "git", &["commit", "-qm", "plaintext while locked"], None);
    run(&repo, "git", &["rm", "-q", "--cached", "late.secret"], None);
    // The locked checkout holds ciphertext and stays usable: it is clean,
    // and switching branches passes records through without the key.
    assert!(run(&repo, "git", &["status", "--porcelain", "--untracked-files=no"], None).is_empty());
    run(&repo, "git", &["checkout", "-q", "HEAD~2"], None);
    run(&repo, "git", &["checkout", "-q", "-"], None);
    // A plaintext secret still cannot be added while locked.
    fs::write(repo.join("new.secret"), b"PLAINTEXT\n").unwrap();
    run_fails(&repo, "git", &["add", "new.secret"], None);
    fs::remove_file(repo.join("new.secret")).unwrap();
    unlock(&repo);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
}

fn worktree_files(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path == root.join(".git") { continue; }
            // Git's names: `/` between components, also on Windows.
            let relative = path.strip_prefix(root).unwrap().to_str().unwrap();
            let relative = if cfg!(windows) { relative.replace('\\', "/") } else { relative.to_owned() };
            if path.is_dir() { walk(&path, root, out) } else { out.push(PathBuf::from(relative)) }
        }
    }
    let mut out = Vec::new();
    walk(root, root, &mut out);
    out.sort();
    out
}

/// Crash safety under real process termination: `lock` and `hydrate` are
/// killed with SIGKILL at many points. After every kill each protected file
/// is exactly its staged ciphertext or its plaintext, no other file appeared
/// in the worktree, and rerunning the operation converges.
#[test]
fn killed_lock_and_hydrate_never_corrupt_or_leave_plaintext_behind() {
    let mut scratch = Scratch::new("kill");
    let repo = scratch.repo("repo");
    for i in 0..20 {
        fs::write(repo.join(format!("dir/f{i}.secret")), format!("plaintext number {i}\n")).unwrap();
    }
    commit_all(&repo, "many secrets");
    let mut files = Vec::new();
    for path in worktree_files(&repo) {
        let name = path.to_str().unwrap().to_owned();
        if name.ends_with(".secret") {
            let plaintext = fs::read(repo.join(&path)).unwrap();
            files.push((path, plaintext, run(&repo, "git", &["show", &format!(":{name}")], None)));
        }
    }
    assert_eq!(files.len(), 22);
    let listing = worktree_files(&repo);
    let start = std::time::Instant::now();
    run(&repo, bin(), &["lock"], None);
    let full = start.elapsed().as_micros() as u64;
    unlock(&repo);
    let live = |repo: &Path| unlocked(repo);
    for round in 0..12u64 {
        let op = if round % 2 == 0 { "lock" } else { "hydrate" };
        if !live(&repo) {
            run(&repo, bin(), &["unlock", "--password-stdin", "--no-hydrate"], Some(PASS));
        }
        let mut child = Command::new(bin()).arg(op).current_dir(&repo)
            .stdout(Stdio::null()).stderr(Stdio::null()).spawn().unwrap();
        std::thread::sleep(Duration::from_micros(full * (round / 2 + 1) / 7));
        let _ = child.kill();
        let _ = child.wait();
        assert_eq!(worktree_files(&repo), listing, "round {round}: unexpected worktree file");
        for (path, plaintext, ciphertext) in &files {
            let now = fs::read(repo.join(path)).unwrap();
            assert!(now == *plaintext || now == *ciphertext, "round {round}: {path:?} corrupted");
        }
        if !live(&repo) {
            run(&repo, bin(), &["unlock", "--password-stdin", "--no-hydrate"], Some(PASS));
        }
        // A Git child of the killed process may still hold `.git/index.lock`
        // for a moment; Git itself then refuses, so retry briefly.
        let mut attempts = 0;
        while !exec(&repo, bin(), &[op], None).status.success() {
            attempts += 1;
            assert!(attempts < 20, "round {round}: {op} cannot resume");
            std::thread::sleep(Duration::from_millis(100));
        }
        for (path, plaintext, ciphertext) in &files {
            let expected = if op == "lock" { ciphertext } else { plaintext };
            assert_eq!(&fs::read(repo.join(path)).unwrap(), expected, "round {round}: {op} did not converge");
        }
        if op == "hydrate" {
            assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty(), "round {round}");
        }
    }
}

/// Private mode: plaintext that Git's checkout wrote with a permissive umask
/// is made private by hydrate (published files are created 0600).
#[test]
fn hydrate_makes_existing_plaintext_private() {
    let mut scratch = Scratch::new("perms");
    let repo = scratch.repo("repo");
    private(&repo);
    make_public(&repo.join("a.secret"));
    assert!(!owner_only(&repo.join("a.secret")));
    run(&repo, bin(), &["hydrate"], None);
    assert!(owner_only(&repo.join("a.secret")));
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
}

/// Files tracked in plaintext before their pattern was protected are
/// encrypted in the index right away, with a warning that their earlier
/// commits stay readable.
#[test]
fn init_encrypts_files_already_tracked_in_plaintext() {
    let mut scratch = Scratch::new("pretracked");
    let repo = scratch.root.join("repo");
    fs::create_dir(&repo).unwrap();
    scratch.repos.push(repo.clone());
    run(&repo, "git", &["init", "-q"], None);
    Scratch::identify(&repo);
    fs::write(repo.join("old.secret"), b"PLAINTEXT IN HISTORY\n").unwrap();
    commit(&repo, &["old.secret"], "plaintext secret");
    let out = exec(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{err}");
    assert!(err.contains("encrypting old.secret") && err.contains("stay readable in earlier commits"), "{err}");
    assert!(is_record(&staged(&repo, "old.secret")));
    assert_eq!(fs::read(repo.join("old.secret")).unwrap(), b"PLAINTEXT IN HISTORY\n");
    run(&repo, "git", &["commit", "-qm", "enable"], None);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    run(&repo, bin(), &["audit"], None);
}

/// A hostile staged or committed blob above the 16 MiB bound is refused
/// without being loaded, by `verify-index` and by `audit`, and refusing it
/// does not disturb later object reads.
#[test]
fn oversized_hostile_blobs_are_refused() {
    let mut scratch = Scratch::new("oversized");
    let repo = scratch.repo("repo");
    let big = vec![b'A'; 16 * 1024 * 1024 + 39];
    let path = scratch.root.join("big");
    fs::write(&path, &big).unwrap();
    let oid = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--no-filters", path.to_str().unwrap()], None)).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", "100644", oid.trim(), "big.secret"], None);
    let err = run_fails(&repo, bin(), &["verify-index"], None);
    assert!(err.contains("16 MiB"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "oversized"], None);
    let err = run_fails(&repo, bin(), &["audit", "HEAD"], None);
    assert!(err.contains("16 MiB") && err.contains("big.secret"), "{err}");
    run(&repo, bin(), &["audit", "HEAD~1"], None);
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&repo, bin(), &["verify-index"], None);
}

/// The agent does not keep descriptors it inherited from `unlock`'s caller:
/// a pipe held open by the agent would hang whoever waits for its EOF.
#[test]
#[cfg(unix)] // Windows creates every handle non-inheritable.
fn agent_does_not_keep_inherited_descriptors() {
    use std::os::fd::AsRawFd;
    let mut scratch = Scratch::new("fds");
    let repo = scratch.repo("repo");
    run(&repo, bin(), &["lock"], None);
    let (mut reader, writer) = std::io::pipe().unwrap();
    let fd = writer.as_raw_fd();
    // Make the write end inheritable, as a shell would leave it.
    unsafe { libc_fcntl_clear_cloexec(fd) };
    let mut child = Command::new(bin()).args(["unlock", "--password-stdin", "--no-hydrate"])
        .current_dir(&repo).stdin(Stdio::piped()).stdout(Stdio::null()).stderr(Stdio::null())
        .spawn().unwrap();
    child.stdin.take().unwrap().write_all(PASS).unwrap();
    assert!(child.wait().unwrap().success());
    drop(writer);
    // EOF arrives only if no process (the agent) still holds the write end.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || { let mut buf = Vec::new(); let _ = reader.read_to_end(&mut buf); let _ = tx.send(()); });
    assert!(rx.recv_timeout(Duration::from_secs(10)).is_ok(), "agent kept an inherited pipe open");
}

#[cfg(unix)]
unsafe fn libc_fcntl_clear_cloexec(fd: i32) {
    extern "C" { fn fcntl(fd: i32, cmd: i32, ...) -> i32; }
    const F_SETFD: i32 = 2;
    fcntl(fd, F_SETFD, 0);
}

/// The shipped server-side hook (`contrib/v3/pre-receive`) refuses a push
/// carrying plaintext even when the client skipped its own pre-push hook.
#[test]
fn server_pre_receive_hook_refuses_plaintext_pushes() {
    let mut scratch = Scratch::new("prereceive");
    let repo = scratch.repo("repo");
    run(&scratch.root, "git", &["init", "-q", "--bare", "remote.git"], None);
    let hook = scratch.root.join("remote.git/hooks/pre-receive");
    fs::copy(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../contrib/v3/pre-receive"), &hook).unwrap();
    run(&repo, "git", &["remote", "add", "origin", "../remote.git"], None);
    let push = |args: &[&str]| {
        let mut command = Command::new("git");
        command.args(args).current_dir(&repo).env("TRANSCRYPT_RS", bin())
            .stdout(Stdio::piped()).stderr(Stdio::piped());
        command.output().unwrap()
    };
    assert!(push(&["push", "-q", "origin", "HEAD:refs/heads/main"]).status.success());
    let blob = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"],
        Some(b"SERVER MUST REFUSE\n"))).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", "100644", blob.trim(), "leak.secret"], None);
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "bypass"], None);
    let out = push(&["push", "-q", "--no-verify", "origin", "HEAD:refs/heads/main"]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success() && err.contains("leak.secret"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
}

/// Run `git` under an explicit umask, as a user's shell would.
fn git_with_umask(dir: &Path, mask: &str, args: &[&str]) {
    let script = format!("umask {mask} && exec git \"$@\"");
    let mut full = vec!["-c", script.as_str(), "git"];
    full.extend_from_slice(args);
    run(dir, "sh", &full, None);
}

/// No protected worktree file holds plaintext while readable by others.
fn assert_no_exposed_plaintext(repo: &Path, step: &str) {
    for path in worktree_files(repo) {
        if !path.to_str().unwrap().ends_with(".secret") { continue; }
        let full = repo.join(&path);
        let bytes = fs::read(&full).unwrap();
        assert!(is_record(&bytes) || owner_only(&full), "{step}: {path:?} is plaintext readable by others");
    }
}

/// Private mode. Regression: with `umask 022`, Git wrote smudged plaintext
/// with mode 0644, readable by every local user. Smudge now releases plaintext only
/// when Git's umask makes the file private; otherwise Git writes the
/// authenticated ciphertext and the post-checkout/post-merge/post-rewrite
/// hooks (or `hydrate`) publish the plaintext with mode 0600.
#[test]
fn git_never_writes_plaintext_readable_by_others() {
    let mut scratch = Scratch::new("umask");
    let repo = scratch.repo("repo");
    private(&repo);
    run(&repo, "git", &["checkout", "-q", "-b", "side"], None);
    fs::write(repo.join("a.secret"), b"alpha on side\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "side change"], None);
    run(&repo, "git", &["checkout", "-q", "-"], None);
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    let main = main.trim();
    // Switching branches: the hook decrypts privately.
    git_with_umask(&repo, "022", &["checkout", "-q", "side"]);
    assert_no_exposed_plaintext(&repo, "checkout");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha on side\n");
    git_with_umask(&repo, "022", &["checkout", "-q", main]);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    // Merge (post-merge) and rebase (post-checkout/post-rewrite).
    fs::write(repo.join("dir/b.secret"), b"beta on main\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "main change"], None);
    git_with_umask(&repo, "022", &["merge", "-q", "--no-edit", "side"]);
    assert_no_exposed_plaintext(&repo, "merge");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha on side\n");
    git_with_umask(&repo, "022", &["checkout", "-q", "side"]);
    git_with_umask(&repo, "022", &["rebase", "-q", main]);
    assert_no_exposed_plaintext(&repo, "rebase");
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), b"beta on main\n");
    git_with_umask(&repo, "022", &["checkout", "-q", main]);
    // Restore and stash run no hook: ciphertext stays until `hydrate`, which
    // also decrypts a stash-popped edit without staging it.
    fs::write(repo.join("a.secret"), b"uncommitted edit\n").unwrap();
    git_with_umask(&repo, "022", &["stash", "-q"]);
    assert_no_exposed_plaintext(&repo, "stash");
    git_with_umask(&repo, "022", &["stash", "pop", "-q"]);
    assert_no_exposed_plaintext(&repo, "stash pop");
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"uncommitted edit\n");
    assert_no_exposed_plaintext(&repo, "hydrate after stash pop");
    assert!(run(&repo, "git", &["diff", "--cached", "--name-only"], None).is_empty());
    git_with_umask(&repo, "022", &["restore", "a.secret"]);
    assert_no_exposed_plaintext(&repo, "restore");
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha on side\n");
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    // With a private umask, smudge writes plaintext directly (mode 0600).
    git_with_umask(&repo, "077", &["checkout", "-q", "HEAD~1"]);
    assert_no_exposed_plaintext(&repo, "private umask");
    git_with_umask(&repo, "077", &["checkout", "-q", main]);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
}

/// The incremental audit (each commit against its first parent) still sees
/// plaintext that enters through a merge's second parent, and a config
/// change re-checks every record against the new config.
#[test]
fn incremental_audit_covers_merges_and_config_changes() {
    let mut scratch = Scratch::new("auditmerge");
    let repo = scratch.repo("repo");
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    let main = main.trim().to_owned();
    run(&repo, "git", &["tag", "published"], None);
    // A side branch commits plaintext without hooks; main merges it.
    run(&repo, "git", &["checkout", "-q", "-b", "side"], None);
    let blob = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"],
        Some(b"MERGED PLAINTEXT\n"))).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", "100644", blob.trim(), "side.secret"], None);
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "plaintext on side"], None);
    run(&repo, "git", &["checkout", "-q", &main], None);
    fs::write(repo.join("README"), b"main moves on\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "main"], None);
    // (Checking the merge out would fail: smudge refuses the plaintext.
    // Build it with plumbing, as a remote attacker could.)
    let tree = String::from_utf8(run(&repo, "git", &["rev-parse", "side^{tree}"], None)).unwrap();
    let merge = String::from_utf8(run(&repo, "git", &["commit-tree", tree.trim(), "-p", "HEAD", "-p", "side", "-m", "merge"], None)).unwrap();
    // Only the merge itself is selected; its first parent is "published".
    let err = run_fails(&repo, bin(), &["audit", merge.trim(), "--not", "HEAD", "side"], None);
    assert!(err.contains("side.secret"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "published"], None);
    // A commit that replaces the config orphans every existing record.
    let mut config = fs::read(repo.join(".transcrypt/config")).unwrap();
    config[10] ^= 1;
    let oid = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"], Some(&config))).unwrap();
    run(&repo, "git", &["update-index", "--cacheinfo", "100644", oid.trim(), ".transcrypt/config"], None);
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "swap config"], None);
    let err = run_fails(&repo, bin(), &["audit", "HEAD", "--not", "published"], None);
    assert!(err.contains("not v3 ciphertext for its configuration"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "published"], None);
    // A work budget refuses oversized audits instead of running unbounded.
    let err = run_fails(&repo, bin(), &["audit", "--max-commits=1", "HEAD"], None);
    assert!(err.contains("more than 1 commits"), "{err}");
}

/// `doctor` passes on a protected checkout and fails, naming the gap, when
/// any local protection is missing or overridden.
#[test]
fn doctor_detects_missing_protection() {
    let mut scratch = Scratch::new("doctor");
    let repo = scratch.repo("repo");
    let out = String::from_utf8(run(&repo, bin(), &["doctor"], None)).unwrap();
    assert!(!out.contains("FAIL"), "{out}");
    let hook = repo.join(".git/hooks/pre-push");
    let saved = fs::read(&hook).unwrap();
    fs::remove_file(&hook).unwrap();
    let out = exec(&repo, bin(), &["doctor"], None);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("FAIL pre-push hook installed"));
    fs::write(&hook, saved).unwrap();
    make_executable(&hook);
    for (key, value) in [("core.hooksPath", "/nonexistent"), ("filter.transcrypt-v3.process", "cat"),
                         ("filter.transcrypt-v3.required", "false")] {
        let original = exec(&repo, "git", &["config", key], None).stdout;
        run(&repo, "git", &["config", key, value], None);
        assert!(!exec(&repo, bin(), &["doctor"], None).status.success(), "{key}");
        if original.is_empty() {
            run(&repo, "git", &["config", "--unset", key], None);
        } else {
            run(&repo, "git", &["config", key, String::from_utf8(original).unwrap().trim_end()], None);
        }
    }
    fs::write(repo.join(".git/info/attributes"), b"*.secret -filter\n").unwrap();
    let out = exec(&repo, bin(), &["doctor"], None);
    assert!(String::from_utf8_lossy(&out.stdout).contains("FAIL no local attribute file overrides"), "{}",
        String::from_utf8_lossy(&out.stdout));
    fs::remove_file(repo.join(".git/info/attributes")).unwrap();
    assert!(exec(&repo, bin(), &["doctor"], None).status.success());
}

/// `contrib/v3/check-remote-enforcement` tells a remote that enforces the
/// audit from one that does not (and cleans up after the unprotected one).
#[test]
fn remote_enforcement_check_detects_unprotected_remotes() {
    let mut scratch = Scratch::new("enforcement");
    let repo = scratch.repo("repo");
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../contrib/v3/check-remote-enforcement");
    let hook = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../contrib/v3/pre-receive");
    for (name, protected) in [("open.git", false), ("guarded.git", true)] {
        run(&scratch.root, "git", &["init", "-q", "--bare", name], None);
        if protected {
            fs::copy(&hook, scratch.root.join(name).join("hooks/pre-receive")).unwrap();
        }
        // Git for Windows' sh runs the script there.
        let mut command = if cfg!(windows) { let mut sh = Command::new("sh"); sh.arg(&script); sh } else { Command::new(&script) };
        let out = command.arg(format!("../{name}")).current_dir(&repo)
            // The variable's name before the rename, still honored.
            .env("TRANSCRYPT_V3", bin()).output().unwrap();
        let text = String::from_utf8_lossy(&out.stderr).to_string() + &String::from_utf8_lossy(&out.stdout);
        assert_eq!(out.status.success(), protected, "{name}: {text}");
        let refs = run(&scratch.root.join(name), "git", &["for-each-ref"], None);
        assert!(refs.is_empty(), "{name}: canary left behind");
    }
}

/// Randomized hostile clients: random opcodes, mutated configs and paths,
/// lying length fields, truncated and garbage frames. The agent never
/// releases plaintext for anything but an exact, authorized request, never
/// stalls on lying lengths beyond its timeout, and keeps serving.
#[test]
fn agent_survives_random_hostile_frames() {
    let mut scratch = Scratch::new("agentfuzz");
    let repo = scratch.repo("repo");
    private(&repo);
    let config = fs::read(repo.join(".transcrypt/config")).unwrap();
    let record = staged(&repo, "a.secret");
    let mut state = 0x51ed_270b_2b3a_44c1u64;
    let mut next = move || { state ^= state << 13; state ^= state >> 7; state ^= state << 17; state };
    for _ in 0..150 {
        let op = [b'P', b'E', b'D', b'X', b'Q', 0][(next() % 6) as usize];
        let mut cfg = config.clone();
        if next() % 3 == 0 { let i = (next() as usize) % cfg.len(); cfg[i] ^= 1 << (next() % 8); }
        let path: &[u8] = [&b"a.secret"[..], b"dir/b.secret", b"../a.secret", b"", b"a.secret\0"][(next() % 5) as usize];
        let mut body = record.clone();
        if next() % 2 == 0 && !body.is_empty() { let i = (next() as usize) % body.len(); body[i] ^= 1; }
        let exact = op == b'D' && cfg == config && path == b"a.secret" && body == record;
        if op == b'X' && cfg == config { continue; } // a valid stop request would end the session
        if next() % 4 == 0 {
            // Garbage or a frame whose length fields lie (claims more than sent).
            let mut stream = UnixStream::connect(socket(&repo)).unwrap();
            let mut frame = vec![op];
            frame.extend_from_slice(&cfg[..(next() as usize) % (cfg.len() + 1)]);
            frame.extend((0..(next() % 64)).map(|_| next() as u8));
            let _ = stream.write_all(&frame);
            drop(stream);
            continue;
        }
        match agent_request(&repo, op, &cfg, path, &body) {
            Ok(plain) if op == b'D' => assert!(exact && plain == b"alpha plaintext\n", "released plaintext for a hostile request"),
            Ok(_) => assert!(matches!(op, b'P' | b'E') && cfg == config, "unexpected success for opcode {op}"),
            Err(_) => assert!(!exact, "refused the genuine request"),
        }
    }
    assert_eq!(agent_request(&repo, b'D', &config, b"a.secret", &record).unwrap(), b"alpha plaintext\n");
}

fn pkt(data: &[u8]) -> Vec<u8> {
    [format!("{:04x}", data.len() + 4).as_bytes(), data].concat()
}

fn read_pkt(r: &mut impl Read) -> Option<Vec<u8>> {
    let mut h = [0u8; 4];
    r.read_exact(&mut h).unwrap();
    let n = usize::from_str_radix(std::str::from_utf8(&h).unwrap(), 16).unwrap();
    if n == 0 { return None; }
    let mut d = vec![0u8; n - 4];
    r.read_exact(&mut d).unwrap();
    Some(d)
}

fn read_until_flush(r: &mut impl Read) -> Vec<u8> {
    let mut all = Vec::new();
    while let Some(d) = read_pkt(r) { all.extend(d); }
    all
}

/// The long-running filter speaks Git's protocol exactly: it converts files
/// through the same gates as the per-file filters, refuses (and survives)
/// oversized or invalid requests, and stops on a malformed packet.
#[test]
fn long_running_filter_protocol() {
    let mut scratch = Scratch::new("process");
    let repo = scratch.repo("repo");
    let record = staged(&repo, "a.secret");
    let mut child = Command::new("sh").args(["-c", &format!("umask 077 && exec '{}' filter-process", bin())])
        .current_dir(&repo).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().unwrap();
    let mut to = child.stdin.take().unwrap();
    let mut from = child.stdout.take().unwrap();
    to.write_all(&[pkt(b"git-filter-client\n"), pkt(b"version=2\n"), b"0000".to_vec(),
        pkt(b"capability=clean\n"), pkt(b"capability=smudge\n"), pkt(b"capability=delay\n"), b"0000".to_vec()].concat()).unwrap();
    assert_eq!(read_until_flush(&mut from), b"git-filter-server\nversion=2\n");
    assert_eq!(read_until_flush(&mut from), b"capability=clean\ncapability=smudge\n");
    let mut request = |command: &str, path: &[u8], content: &[u8]| -> (Vec<u8>, Vec<u8>) {
        let mut frame = [pkt(format!("command={command}\n").as_bytes()), pkt(&[b"pathname=", path, b"\n"].concat()), b"0000".to_vec()].concat();
        for chunk in content.chunks(65516) { frame.extend(pkt(chunk)); }
        frame.extend(b"0000");
        to.write_all(&frame).unwrap();
        let status = read_until_flush(&mut from);
        if status != b"status=success\n" { return (status, Vec::new()); }
        let body = read_until_flush(&mut from);
        assert!(read_until_flush(&mut from).is_empty());
        (status, body)
    };
    assert_eq!(request("smudge", b"a.secret", &record), (b"status=success\n".to_vec(), b"alpha plaintext\n".to_vec()));
    assert_eq!(request("clean", b"a.secret", b"alpha plaintext\n").1, record);
    // A record moved to another path does not authenticate there.
    assert_eq!(request("smudge", b"dir/b.secret", &record).0, b"status=error\n");
    assert_eq!(request("clean", b"../x.secret", b"x").0, b"status=error\n");
    // Oversized content is read to its end and refused; the session goes on.
    assert_eq!(request("clean", b"a.secret", &vec![b'x'; 16 * 1024 * 1024 + 39]).0, b"status=error\n");
    assert_eq!(request("smudge", b"a.secret", &record).1, b"alpha plaintext\n");
    // A malformed packet ends the process with an error.
    to.write_all(b"00G0").unwrap();
    drop(to);
    assert!(!child.wait().unwrap().success());
}

/// `uninstall` locks first, removes only what v3 installed (filters, its
/// unchanged hooks, its ignore rules), leaves ciphertext in the worktree and
/// a clean status, and refuses while plaintext would be left unprotected.
#[test]
fn uninstall_removes_v3_and_leaves_only_ciphertext() {
    let mut scratch = Scratch::new("uninstall");
    let repo = scratch.repo("repo");
    fs::write(repo.join(".git/info/exclude"), b"# mine\n*.log\n").unwrap();
    run(&repo, bin(), &["lock"], None);
    unlock(&repo);
    // A plaintext edit is not lost: lock (and so uninstall) refuses.
    fs::write(repo.join("a.secret"), b"unsaved edit\n").unwrap();
    run_fails(&repo, bin(), &["uninstall"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"unsaved edit\n");
    run(&repo, "git", &["checkout", "--", "a.secret"], None);
    run(&repo, bin(), &["hydrate"], None);
    run(&repo, bin(), &["uninstall"], None);
    assert!(is_record(&fs::read(repo.join("a.secret")).unwrap()));
    assert!(exec(&repo, "git", &["config", "--get-regexp", "filter.transcrypt-v3"], None).stdout.is_empty());
    for hook in ["pre-commit", "pre-push", "post-checkout"] {
        assert!(!repo.join(".git/hooks").join(hook).exists(), "{hook}");
    }
    assert_eq!(fs::read(repo.join(".git/info/exclude")).unwrap(), b"# mine\n*.log\n");
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    assert!(!repo.join(".git/transcrypt-v3").exists());
    // Unlocking reinstalls everything.
    unlock(&repo);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert!(exec(&repo, bin(), &["doctor"], None).status.success());
}

/// `rekey` re-encrypts every secret under a new passphrase in one staged
/// change, refuses to mix in uncommitted edits, and leaves history readable
/// with the old passphrase only.
#[test]
fn rekey_rotates_the_passphrase() {
    let mut scratch = Scratch::new("rekey");
    let repo = scratch.repo("repo");
    const NEW: &[u8] = b"a completely different long passphrase\n";
    fs::write(repo.join("a.secret"), b"uncommitted\n").unwrap();
    let err = run_fails(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    assert!(err.contains("uncommitted changes"), "{err}");
    run(&repo, "git", &["checkout", "--", "a.secret"], None);
    let before = run(&repo, "git", &["rev-parse", "HEAD"], None);
    run(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    // Config and both records are staged; the worktree is still plaintext.
    let staged = run(&repo, "git", &["diff", "--cached", "--name-only"], None);
    assert_eq!(staged, b".transcrypt/config\na.secret\ndir/b.secret\n");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert!(run(&repo, "git", &["status", "--porcelain", "--untracked-files=no"], None)
        .split(|b| *b == b'\n').all(|l| l.is_empty() || l.starts_with(b"M ")));
    run(&repo, "git", &["commit", "-qm", "rekey"], None);
    run(&repo, bin(), &["audit"], None);
    run(&repo, bin(), &["lock"], None);
    run_fails(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(NEW));
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), b"beta plaintext\n");
    // The old commit still needs (and opens with) the old passphrase.
    let old = String::from_utf8(before).unwrap();
    let old_config = run(&repo, "git", &["show", &format!("{}:.transcrypt/config", old.trim())], None);
    assert_ne!(old_config, fs::read(repo.join(".transcrypt/config")).unwrap());
}

/// A protected file deleted in the worktree (or absent in a sparse
/// checkout) holds no plaintext: it no longer blocks `lock`, `hydrate` or
/// `unlock` for every other file, and stays deleted.
#[test]
fn deleted_protected_files_do_not_block_lock_or_hydrate() {
    let mut scratch = Scratch::new("deleted");
    let repo = scratch.repo("repo");
    fs::remove_file(repo.join("dir/b.secret")).unwrap();
    fs::remove_dir(repo.join("dir")).unwrap();
    run(&repo, bin(), &["lock"], None);
    assert!(is_record(&fs::read(repo.join("a.secret")).unwrap()));
    assert!(!repo.join("dir").exists());
    unlock(&repo);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    assert!(status.contains("deleted") && status.contains("dir/b.secret"), "{status}");
    run(&repo, "git", &["checkout", "--", "dir/b.secret"], None);
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), b"beta plaintext\n");
}

/// Concurrent edits of one secret merge like plaintext: non-overlapping
/// edits merge automatically, and a conflict shows decrypted conflict
/// markers (in private mode: mode 0600, after `hydrate` under a permissive umask) that are
/// resolved and committed as usual. The merged record stays encrypted.
#[test]
fn secrets_merge_as_plaintext() {
    let mut scratch = Scratch::new("merge");
    let repo = scratch.repo("repo");
    private(&repo);
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    let main = main.trim().to_owned();
    fs::write(repo.join("a.secret"), b"one\ntwo\nthree\nfour\nfive\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "base"], None);
    run(&repo, "git", &["branch", "side"], None);
    // Non-overlapping edits merge cleanly.
    fs::write(repo.join("a.secret"), b"ONE\ntwo\nthree\nfour\nfive\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "main edit"], None);
    git_with_umask(&repo, "022", &["checkout", "-q", "side"]);
    fs::write(repo.join("a.secret"), b"one\ntwo\nthree\nfour\nFIVE\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "side edit"], None);
    git_with_umask(&repo, "022", &["checkout", "-q", &main]);
    git_with_umask(&repo, "022", &["merge", "-q", "--no-edit", "side"]);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"ONE\ntwo\nthree\nfour\nFIVE\n");
    assert!(is_record(&staged(&repo, "a.secret")));
    assert_no_exposed_plaintext(&repo, "clean merge");
    // Overlapping edits conflict; the markers are decrypted for resolution.
    // Windows never treats a checkout as private: hydrate always decrypts.
    for (mask, needs_hydrate) in [("022", true), ("077", cfg!(windows))] {
        fs::write(repo.join("a.secret"), b"ONE\nmain two\n").unwrap();
        run(&repo, "git", &["commit", "-qam", "main conflict"], None);
        git_with_umask(&repo, mask, &["checkout", "-q", "side"]);
        fs::write(repo.join("a.secret"), b"ONE\nside two\n").unwrap();
        run(&repo, "git", &["commit", "-qam", "side conflict"], None);
        git_with_umask(&repo, mask, &["checkout", "-q", &main]);
        let out = exec(&repo, "sh", &["-c", &format!("umask {mask} && exec git merge -q --no-edit side")], None);
        assert!(!out.status.success(), "conflicting merge succeeded");
        assert_no_exposed_plaintext(&repo, "conflicted merge");
        let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
        assert!(status.contains("conflicted"), "{status}");
        if needs_hydrate { run(&repo, bin(), &["hydrate"], None); }
        let conflicted = String::from_utf8(fs::read(repo.join("a.secret")).unwrap()).unwrap();
        assert!(conflicted.contains("<<<<<<< ours") && conflicted.contains("main two")
            && conflicted.contains("side two") && conflicted.contains(">>>>>>> theirs"), "{conflicted}");
        assert_no_exposed_plaintext(&repo, "hydrated conflict");
        fs::write(repo.join("a.secret"), b"ONE\nresolved two\n").unwrap();
        commit(&repo, &["a.secret"], "resolved");
        assert!(is_record(&staged(&repo, "a.secret")));
        run(&repo, bin(), &["verify-index"], None);
        // Make side match main again for the next round.
        git_with_umask(&repo, mask, &["checkout", "-q", "side"]);
        git_with_umask(&repo, mask, &["merge", "-q", "--no-edit", &main]);
        git_with_umask(&repo, mask, &["checkout", "-q", &main]);
    }
    run(&repo, bin(), &["audit"], None);
}

/// A merge `git merge-file` cannot do (binary secrets; it exits with 255,
/// not a conflict count) fails, and our side stays exactly as it was.
#[test]
fn a_failed_merge_never_replaces_our_side() {
    let mut scratch = Scratch::new("mergefail");
    let repo = scratch.repo("repo");
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    fs::write(repo.join("a.secret"), b"base\0binary\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "binary base"], None);
    run(&repo, "git", &["checkout", "-q", "-b", "side"], None);
    fs::write(repo.join("a.secret"), b"side\0binary\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "side"], None);
    run(&repo, "git", &["checkout", "-q", main.trim()], None);
    fs::write(repo.join("a.secret"), b"ours\0binary\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "ours"], None);
    let out = exec(&repo, "git", &["merge", "-q", "--no-edit", "side"], None);
    assert!(!out.status.success(), "a binary conflict cannot merge");
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"ours\0binary\n");
    run(&repo, "git", &["merge", "--abort"], None);
}

/// Plaintext inputs left by a merge driver that crashed are removed by the
/// next merge.
#[test]
fn crashed_merge_inputs_are_purged() {
    let mut scratch = Scratch::new("mergecrash");
    let repo = scratch.repo("repo");
    let dir = repo.join(".git/transcrypt-v3-scratch");
    fs::create_dir(&dir).unwrap();
    make_private_dir(&dir);
    fs::write(dir.join("2147483646-ours"), b"LEFTOVER PLAINTEXT\n").unwrap();
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    run(&repo, "git", &["checkout", "-q", "-b", "side"], None);
    fs::write(repo.join("a.secret"), b"side\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "side"], None);
    run(&repo, "git", &["checkout", "-q", main.trim()], None);
    fs::write(repo.join("a.secret"), b"main\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "main"], None);
    let _ = exec(&repo, "git", &["merge", "-q", "--no-edit", "side"], None);
    assert_eq!(fs::read_dir(&dir).unwrap().count(), 0, "merge inputs left behind");
    run(&repo, "git", &["merge", "--abort"], None);
}

/// `git diff` shows decrypted diffs of secrets while unlocked (worktree and
/// history alike), leaves no plaintext behind, and while locked only says
/// that the files differ.
#[test]
fn git_diff_shows_decrypted_changes() {
    let mut scratch = Scratch::new("diff");
    let repo = scratch.repo("repo");
    fs::write(repo.join("a.secret"), b"alpha edited\n").unwrap();
    let diff = String::from_utf8(run(&repo, "git", &["diff"], None)).unwrap();
    assert!(diff.contains("-alpha plaintext") && diff.contains("+alpha edited") && diff.contains("a/a.secret"), "{diff}");
    run(&repo, "git", &["commit", "-qam", "edit"], None);
    let diff = String::from_utf8(run(&repo, "git", &["diff", "HEAD~1", "HEAD"], None)).unwrap();
    assert!(diff.contains("-alpha plaintext") && diff.contains("+alpha edited"), "{diff}");
    let log = String::from_utf8(run(&repo, "git", &["log", "-p", "--ext-diff", "-1"], None)).unwrap();
    assert!(log.contains("+alpha edited"), "{log}");
    assert_eq!(fs::read_dir(repo.join(".git/transcrypt-v3-scratch")).unwrap().count(), 0);
    run(&repo, bin(), &["lock"], None);
    let diff = String::from_utf8(run(&repo, "git", &["diff", "HEAD~1", "HEAD"], None)).unwrap();
    assert!(diff.contains("unlock to see the decrypted diff") && !diff.contains("alpha"), "{diff}");
}

/// `unlock` and `lock` are idempotent: unlocking again needs no passphrase
/// and hydrates; locking again succeeds when no plaintext is left, and
/// refuses (without an agent to help) when some is.
#[test]
fn unlock_and_lock_are_idempotent() {
    let mut scratch = Scratch::new("idempotent");
    let repo = scratch.repo("repo");
    run(&repo, bin(), &["unlock"], None);
    run(&repo, bin(), &["lock"], None);
    run(&repo, bin(), &["lock"], None);
    fs::write(repo.join("a.secret"), b"plaintext written while locked\n").unwrap();
    let err = run_fails(&repo, bin(), &["lock"], None);
    assert!(err.contains("a.secret holds plaintext"), "{err}");
    run(&repo, "git", &["checkout", "--", "a.secret"], None);
    run(&repo, bin(), &["lock"], None);
}

/// Linked worktrees share the repository's key, hooks and drivers: one
/// unlock decrypts every worktree, each with its own private staging, and
/// commits made in a linked worktree are encrypted and verified.
#[test]
fn linked_worktrees_share_one_unlocked_session() {
    let mut scratch = Scratch::new("worktree");
    let repo = scratch.repo("repo");
    let linked = scratch.root.join("linked");
    run(&repo, "git", &["worktree", "add", "-q", "-b", "feature", linked.to_str().unwrap()], None);
    assert_eq!(fs::read(linked.join("a.secret")).unwrap(), b"alpha plaintext\n");
    fs::write(linked.join("dir/b.secret"), b"beta from the linked worktree\n").unwrap();
    run(&linked, "git", &["commit", "-qam", "edit in linked worktree"], None);
    assert!(is_record(&staged(&linked, "dir/b.secret")));
    run(&linked, bin(), &["verify-index"], None);
    run(&linked, bin(), &["status"], None);
    // Locking from one worktree flushes every worktree, then stops the
    // shared agent; a plaintext edit in any of them refuses the lock.
    fs::write(linked.join("a.secret"), b"unsaved edit\n").unwrap();
    run_fails(&repo, bin(), &["lock"], None);
    assert_eq!(fs::read(linked.join("a.secret")).unwrap(), b"unsaved edit\n");
    run(&linked, "git", &["checkout", "--", "a.secret"], None);
    run(&repo, bin(), &["lock"], None);
    assert!(is_record(&fs::read(linked.join("a.secret")).unwrap()));
    assert!(is_record(&fs::read(repo.join("a.secret")).unwrap()));
    run(&linked, bin(), &["lock"], None);
    unlock(&linked);
    assert_eq!(fs::read(linked.join("dir/b.secret")).unwrap(), b"beta from the linked worktree\n");
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    scratch.repos.push(linked);
}

/// A v3 repository used as a submodule (its `.git` is a file pointing into
/// the superproject) unlocks, decrypts and locks on its own.
#[test]
fn submodules_are_independent_v3_repositories() {
    let mut scratch = Scratch::new("submodule");
    let inner = scratch.repo("inner");
    run(&inner, bin(), &["lock"], None);
    let outer = scratch.root.join("outer");
    fs::create_dir(&outer).unwrap();
    run(&outer, "git", &["init", "-q"], None);
    run(&outer, "git", &["-c", "protocol.file.allow=always", "submodule", "add", "-q", "../inner", "inner"], None);
    let sub = outer.join("inner");
    assert!(fs::symlink_metadata(sub.join(".git")).unwrap().is_file());
    unlock(&sub);
    assert_eq!(fs::read(sub.join("a.secret")).unwrap(), b"alpha plaintext\n");
    run(&sub, bin(), &["lock"], None);
    assert!(is_record(&fs::read(sub.join("a.secret")).unwrap()));
}

/// Private mode: a secret created under a permissive umask is made private
/// as soon as Git stages it (the clean filter sees its plaintext).
#[test]
fn staging_a_new_secret_makes_it_private() {
    let mut scratch = Scratch::new("addprivate");
    let repo = scratch.repo("repo");
    private(&repo);
    fs::write(repo.join("new.secret"), b"fresh secret\n").unwrap();
    make_public(&repo.join("new.secret"));
    run(&repo, "git", &["add", "new.secret"], None);
    assert!(owner_only(&repo.join("new.secret")));
    run(&repo, "git", &["commit", "-qm", "new secret"], None);
}

/// After pulling a collaborator's rekey, the agent still holding the old key
/// retires itself: `unlock` with the new passphrase works, and `lock` leaves
/// no agent behind.
#[test]
fn pulled_rekey_retires_the_stale_agent() {
    const NEW: &[u8] = b"a completely different long passphrase\n";
    let mut scratch = Scratch::new("pulledrekey");
    let origin = scratch.repo("origin");
    let clone = scratch.clone("origin", "clone");
    run(&clone, bin(), &["unlock", "--private", "--password-stdin"], Some(PASS));
    run(&origin, bin(), &["rekey", "--password-stdin"], Some(NEW));
    run(&origin, "git", &["commit", "-qm", "rekey"], None);
    run(&clone, "git", &["pull", "-q", "--no-rebase"], None);
    run(&clone, bin(), &["unlock", "--private", "--password-stdin"], Some(NEW));
    assert_eq!(fs::read(clone.join("a.secret")).unwrap(), b"alpha plaintext\n");
    run(&clone, bin(), &["lock"], None);
    assert!(!socket(&clone).exists(), "an agent survived lock");
    // Without unlocking again, lock alone also retires a stale agent.
    run(&clone, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&clone, bin(), &["unlock", "--private", "--password-stdin"], Some(PASS));
    run(&clone, "git", &["pull", "-q", "--no-rebase"], None);
    run(&clone, bin(), &["lock"], None);
    std::thread::sleep(Duration::from_millis(300));
    assert!(!socket(&clone).exists(), "a stale agent survived lock");
}

/// A crafted tree may list a path twice (`git mktree` accepts it, `git fsck`
/// refuses it). With such a tree as `HEAD` and `HEAD^1`, `dir/b.secret`'s
/// record staged as `a.secret` must not count as unchanged: the hook (with
/// and without the key) and `verify-index` refuse the snapshot instead of
/// trusting either of its entries.
#[test]
fn trees_listing_a_path_twice_are_refused() {
    let mut scratch = Scratch::new("duptree");
    for moved_first in [true, false] {
        let repo = scratch.repo(if moved_first { "first" } else { "second" });
        let oid = |rev: &str| String::from_utf8(run(&repo, "git", &["rev-parse", rev], None)).unwrap().trim().to_owned();
        let (a, b) = (oid("HEAD:a.secret"), oid("HEAD:dir/b.secret"));
        let listing = String::from_utf8(run(&repo, "git", &["ls-tree", "HEAD"], None)).unwrap();
        let mut tree: String = listing.lines().filter(|l| !l.ends_with("\ta.secret")).map(|l| format!("{l}\n")).collect();
        let (x, y) = if moved_first { (&b, &a) } else { (&a, &b) };
        tree.push_str(&format!("100644 blob {x}\ta.secret\n100644 blob {y}\ta.secret\n"));
        let tree = String::from_utf8(run(&repo, "git", &["mktree"], Some(tree.as_bytes()))).unwrap();
        let first = String::from_utf8(run(&repo, "git", &["commit-tree", tree.trim(), "-p", "HEAD", "-m", "dup"], None)).unwrap();
        let second = String::from_utf8(run(&repo, "git", &["commit-tree", tree.trim(), "-p", first.trim(), "-m", "dup"], None)).unwrap();
        run(&repo, "git", &["reset", "-q", "--soft", second.trim()], None);
        // The keyed audit refuses that history (the record does not open there).
        run_fails(&repo, bin(), &["audit", "HEAD"], None);
        run(&repo, "git", &["update-index", "--cacheinfo", &format!("100644,{b},a.secret")], None);
        fs::write(repo.join("z"), b"z\n").unwrap();
        run(&repo, "git", &["add", "z"], None);
        for locked in [false, true] {
            if locked {
                // `lock` verifies the index against `HEAD` first, so it refuses too.
                let err = run_fails(&repo, bin(), &["lock"], None);
                assert!(err.contains("lists a path twice"), "{err}");
                fs::remove_file(repo.join(".git/transcrypt-v3/key")).unwrap();
            }
            // The hook Git runs (the locked worktree's plaintext would fail clean first).
            let err = if locked { run_fails(&repo, bin(), &["pre-commit"], None) }
                else { run_fails(&repo, "git", &["commit", "-qm", "moved record"], None) };
            assert!(err.contains("lists a path twice"), "{err}");
            let err = run_fails(&repo, bin(), &["verify-index"], None);
            assert!(err.contains("lists a path twice"), "{err}");
        }
        assert_eq!(oid("HEAD"), second.trim(), "a commit was made");
    }
}

/// An entry unchanged since `HEAD` and `HEAD^1` counts as already checked
/// only while the selection is unchanged: a record copied to an unprotected
/// name in history and protected afterwards was never authenticated there,
/// so the hook authenticates it (as the audit does) and refuses it.
#[test]
fn newly_protected_files_are_authenticated_by_the_hook() {
    let mut scratch = Scratch::new("newlyprotected");
    let repo = scratch.repo("repo");
    let record = String::from_utf8(run(&repo, "git", &["rev-parse", "HEAD:a.secret"], None)).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", &format!("100644,{},c.data", record.trim())], None);
    run(&repo, "git", &["commit", "-qm", "copy", "--no-verify"], None);
    fs::write(repo.join("README"), b"edited\n").unwrap();
    commit(&repo, &["README"], "unrelated");
    let mut attributes = fs::read(repo.join(".gitattributes")).unwrap();
    attributes.extend_from_slice(b"*.data transcrypt\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    run(&repo, "git", &["add", ".gitattributes"], None);
    let err = run_fails(&repo, bin(), &["pre-commit"], None);
    assert!(err.contains("c.data") && err.contains("authentication failed"), "{err}");
}
