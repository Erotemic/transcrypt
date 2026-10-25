//! Adversarial and fault-recovery lifecycle tests (roadmap stage V5) against
//! real Git repositories and the real credential agent.
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::{fs, time::Duration};

const PASS: &[u8] = b"long correct horse battery staple test passphrase\n";

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_transcrypt-v3")
}

fn exec(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> Output {
    let mut command = Command::new(name);
    command.args(args).current_dir(dir).stdout(Stdio::piped()).stderr(Stdio::piped());
    if input.is_some() {
        command.stdin(Stdio::piped());
    }
    let mut child = command.spawn().unwrap();
    if let Some(value) = input {
        child.stdin.take().unwrap().write_all(value).unwrap();
    }
    child.wait_with_output().unwrap()
}

fn run(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> Vec<u8> {
    let out = exec(dir, name, args, input);
    assert!(out.status.success(), "{name} {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
    out.stdout
}

fn run_fails(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> String {
    let out = exec(dir, name, args, input);
    assert!(!out.status.success(), "{name} {args:?} unexpectedly succeeded");
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// A scratch directory removed (and any agent stopped) when the test ends.
struct Scratch {
    root: PathBuf,
    repos: Vec<PathBuf>,
}

impl Scratch {
    fn new(tag: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "transcrypt-v3-adv-{tag}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        Scratch { root, repos: Vec::new() }
    }

    /// An initialized, unlocked v3 repository with two committed secrets.
    fn repo(&mut self, name: &str) -> PathBuf {
        let repo = self.root.join(name);
        fs::create_dir(&repo).unwrap();
        run(&repo, "git", &["init", "-q"], None);
        run(&repo, "git", &["config", "user.name", "Example"], None);
        run(&repo, "git", &["config", "user.email", "example@example.test"], None);
        fs::write(repo.join("README"), b"public\n").unwrap();
        run(&repo, "git", &["add", "README"], None);
        run(&repo, "git", &["commit", "-qm", "seed"], None);
        run(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
        fs::create_dir(repo.join("dir")).unwrap();
        fs::write(repo.join("a.secret"), b"alpha plaintext\n").unwrap();
        fs::write(repo.join("dir/b.secret"), b"beta plaintext\n").unwrap();
        run(&repo, "git", &["add", "-A"], None);
        run(&repo, "git", &["commit", "-qm", "secrets"], None);
        self.repos.push(repo.clone());
        repo
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        for repo in &self.repos {
            let _ = exec(repo, bin(), &["lock"], None);
            // Stop a still-running agent even if lock refused.
            if let Ok(config) = fs::read(repo.join(".transcrypt/config")) {
                let _ = agent_request(repo, b'X', &config, b"", b"");
            }
        }
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn staged(repo: &Path, path: &str) -> Vec<u8> {
    run(repo, "git", &["show", &format!(":{path}")], None)
}

fn socket(repo: &Path) -> PathBuf {
    repo.join(".git/transcrypt-v3/session.sock")
}

/// Speak the agent's framing directly, as a hostile same-UID client could.
fn agent_request(repo: &Path, op: u8, config: &[u8], path: &[u8], body: &[u8]) -> Result<Vec<u8>, String> {
    let mut stream = UnixStream::connect(socket(repo)).map_err(|e| e.to_string())?;
    stream.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    let mut frame = vec![op];
    frame.extend_from_slice(config);
    frame.extend_from_slice(&(path.len() as u32).to_be_bytes());
    frame.extend_from_slice(path);
    frame.extend_from_slice(&(body.len() as u32).to_be_bytes());
    frame.extend_from_slice(body);
    stream.write_all(&frame).map_err(|e| e.to_string())?;
    let mut header = [0u8; 5];
    stream.read_exact(&mut header).map_err(|e| e.to_string())?;
    let mut value = vec![0u8; u32::from_be_bytes(header[1..5].try_into().unwrap()) as usize];
    stream.read_exact(&mut value).map_err(|e| e.to_string())?;
    if header[0] == 0 { Ok(value) } else { Err(String::from_utf8_lossy(&value).into_owned()) }
}

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
    assert!(!socket(&repo).exists());

    run(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["hydrate"], None);
    // An unstaged edit is the user's only copy: lock must refuse and keep it.
    fs::write(repo.join("dir/b.secret"), b"unsaved edit\n").unwrap();
    run_fails(&repo, bin(), &["lock"], None);
    assert_eq!(fs::read(repo.join("dir/b.secret")).unwrap(), b"unsaved edit\n");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert!(socket(&repo).exists(), "a refused lock keeps the key available");
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
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(&staging, fs::Permissions::from_mode(0o700)).unwrap();
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
    std::os::unix::fs::symlink(repo.join("dir"), &staging).unwrap();
    fs::write(repo.join("a.secret"), staged(&repo, "a.secret")).unwrap();
    run_fails(&repo, bin(), &["hydrate"], None);
    fs::remove_file(&staging).unwrap();
}

#[test]
fn symlinked_protected_files_are_never_followed() {
    let mut scratch = Scratch::new("symlink");
    let repo = scratch.repo("repo");
    let outside = scratch.root.join("outside.secret");
    let record = staged(&repo, "a.secret");
    fs::write(&outside, &record).unwrap();
    fs::remove_file(repo.join("a.secret")).unwrap();
    std::os::unix::fs::symlink(&outside, repo.join("a.secret")).unwrap();
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
    run_fails(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["lock"], None);
    // A dead agent leaves its socket inode behind; it has no listener.
    drop(UnixListener::bind(socket(&repo)).unwrap());
    assert!(socket(&repo).exists());
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    run(&repo, bin(), &["verify-index"], None);
    // A regular file squatting on the socket path is never removed.
    run(&repo, bin(), &["lock"], None);
    fs::write(socket(&repo), b"not a socket").unwrap();
    run_fails(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    fs::remove_file(socket(&repo)).unwrap();
}

#[test]
fn agent_refuses_hostile_requests_and_keeps_serving() {
    let mut scratch = Scratch::new("agent");
    let repo = scratch.repo("repo");
    let config = fs::read(repo.join(".transcrypt/config")).unwrap();
    let record = staged(&repo, "a.secret");
    assert_eq!(agent_request(&repo, b'D', &config, b"a.secret", &record).unwrap(), b"alpha plaintext\n");
    let mut foreign = config.clone();
    foreign[20] ^= 1;
    for (op, cfg, path, body) in [
        (b'D', &foreign, &b"a.secret"[..], &record[..]),   // different public config
        (b'D', &config, b"dir/b.secret", &record[..]),     // cross-path replay
        (b'D', &config, b"../a.secret", &record[..]),      // noncanonical path
        (b'D', &config, b"a.txt", &record[..]),            // unprotected path
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
    assert!(help.contains("transcrypt-v3 unlock") && help.contains("*.secret"));
    let repo = scratch.repo("repo");
    let text = |repo: &Path| String::from_utf8(run(repo, bin(), &["status"], None)).unwrap();
    use std::os::unix::fs::PermissionsExt;
    for f in ["a.secret", "dir/b.secret"] {
        fs::set_permissions(repo.join(f), fs::Permissions::from_mode(0o644)).unwrap();
    }
    let unlocked = text(&repo);
    assert!(unlocked.contains("session:    unlocked"), "{unlocked}");
    assert!(unlocked.contains("2 decrypted *.secret file(s) are readable by other users"), "{unlocked}");
    for f in ["a.secret", "dir/b.secret"] {
        fs::set_permissions(repo.join(f), fs::Permissions::from_mode(0o600)).unwrap();
    }
    assert!(!text(&repo).contains("readable by other users"));
    assert!(unlocked.contains("2 plaintext"), "{unlocked}");
    fs::write(repo.join("a.secret"), b"edited\n").unwrap();
    fs::write(repo.join("new.secret"), b"untracked\n").unwrap();
    let edited = text(&repo);
    assert!(edited.contains("modified") && edited.contains("1 untracked"), "{edited}");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"edited\n", "status is read-only");
    fs::remove_file(repo.join("new.secret")).unwrap();
    fs::write(repo.join("a.secret"), b"alpha plaintext\n").unwrap();
    run(&repo, bin(), &["lock"], None);
    let locked = text(&repo);
    assert!(locked.contains("session:    locked") && locked.contains("2 ciphertext"), "{locked}");
}

#[cfg(target_os = "linux")]
#[test]
fn key_agent_is_not_dumpable_or_ptrace_readable() {
    use std::os::fd::AsRawFd;
    let mut scratch = Scratch::new("dump");
    let repo = scratch.repo("repo");
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
    use std::os::unix::fs::PermissionsExt;
    let scratch = Scratch::new("rollback");
    let repo = scratch.root.join("repo");
    fs::create_dir(&repo).unwrap();
    run(&repo, "git", &["init", "-q"], None);
    // A regular file squatting on the socket path makes agent startup fail.
    let dir = repo.join(".git/transcrypt-v3");
    fs::create_dir(&dir).unwrap();
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
    fs::write(dir.join("session.sock"), b"squatter").unwrap();
    let err = run_fails(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
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
    let clone = scratch.root.join("clone");
    run(&scratch.root, "git", &["clone", "-q", "repo", "clone"], None);
    scratch.repos.push(clone.clone());
    run(&clone, bin(), &["unlock", "--password-stdin"], Some(PASS));
    assert_eq!(fs::read(clone.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert_eq!(fs::read(clone.join("dir/b.secret")).unwrap(), b"beta plaintext\n");
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    run(&clone, bin(), &["lock"], None);
    // An unexpected local edit: unlock succeeds, hydration changes nothing.
    fs::write(clone.join("dir/b.secret"), b"local edit\n").unwrap();
    let out = exec(&clone, bin(), &["unlock", "--password-stdin"], Some(PASS));
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("hydration changed nothing"));
    assert_ne!(fs::read(clone.join("a.secret")).unwrap(), b"alpha plaintext\n");
    assert_eq!(fs::read(clone.join("dir/b.secret")).unwrap(), b"local edit\n");
    fs::write(clone.join("dir/b.secret"), run(&clone, "git", &["show", ":dir/b.secret"], None)).unwrap();
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
    fs::write(repo.join("sub/:(glob)*.secret"), b"decoy two\n").unwrap();
    run(&repo, "git", &["add", "sub"], None);
    run(&repo, "git", &["commit", "-qm", "hostile names"], None);
    run(&repo, bin(), &["lock"], None);
    fs::write(repo.join("sub/a.secret"), b"UNTRACKED PLAINTEXT\n").unwrap();
    fs::write(repo.join("sub/b.secret"), b"UNTRACKED PLAINTEXT\n").unwrap();
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    let staged = run(&repo, "git", &["ls-files", "-z", "sub"], None);
    assert_eq!(staged, b"sub/.gitattributes\0sub/:(glob)*.secret\0sub/[a].secret\0", "untracked file staged");
    assert_eq!(fs::read(repo.join("sub/[a].secret")).unwrap(), b"decoy\n");
    assert_eq!(fs::read(repo.join("sub/:(glob)*.secret")).unwrap(), b"decoy two\n");
    let status = run(&repo, "git", &["status", "--porcelain", "--untracked-files=no"], None);
    assert!(status.is_empty(), "{}", String::from_utf8_lossy(&status));
    fs::remove_file(repo.join("sub/a.secret")).unwrap();
    fs::remove_file(repo.join("sub/b.secret")).unwrap();
}

/// Regression: staged objects were read with `git show :<path>`, so a
/// protected file named `0:a.secret` was read as stage 0 of `a.secret`.
/// Objects are now read by the object id of the verified index snapshot.
#[test]
fn staged_objects_are_read_by_object_id_not_revision_syntax() {
    let mut scratch = Scratch::new("revsyntax");
    let repo = scratch.repo("repo");
    fs::write(repo.join("0:a.secret"), b"colon plaintext\n").unwrap();
    run(&repo, "git", &["add", "0:a.secret"], None);
    run(&repo, "git", &["commit", "-qm", "colon name"], None);
    run(&repo, bin(), &["verify-index"], None);
    run(&repo, bin(), &["lock"], None);
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
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
    run_fails(&repo, "git", &["commit", "-qm", "blocked by pre-commit"], None);
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
    run(&clone, "git", &["config", "user.name", "Example"], None);
    run(&clone, "git", &["config", "user.email", "example@example.test"], None);
    fs::write(clone.join("new.secret"), b"FRESH CLONE PLAINTEXT\n").unwrap();
    run(&clone, "git", &["add", "new.secret"], None);
    run(&clone, "git", &["commit", "-qm", "unfiltered"], None);
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
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
}

fn worktree_files(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path == root.join(".git") { continue; }
            if path.is_dir() { walk(&path, root, out) } else { out.push(path.strip_prefix(root).unwrap().to_path_buf()) }
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
    run(&repo, "git", &["add", "-A"], None);
    run(&repo, "git", &["commit", "-qm", "many secrets"], None);
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
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
    let live = |repo: &Path| repo.join(".git/transcrypt-v3/session.sock").exists();
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

/// Plaintext that Git's checkout wrote with a permissive umask is made
/// private by hydrate (published files are created 0600).
#[test]
fn hydrate_makes_existing_plaintext_private() {
    use std::os::unix::fs::PermissionsExt;
    let mut scratch = Scratch::new("perms");
    let repo = scratch.repo("repo");
    fs::set_permissions(repo.join("a.secret"), fs::Permissions::from_mode(0o644)).unwrap();
    fs::write(repo.join("KEY.SECRET"), b"looks protected\n").unwrap();
    let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    assert!(status.contains("readable by other users"), "{status}");
    assert!(status.contains("KEY.SECRET is NOT encrypted"), "{status}");
    fs::remove_file(repo.join("KEY.SECRET")).unwrap();
    run(&repo, bin(), &["hydrate"], None);
    assert_eq!(fs::metadata(repo.join("a.secret")).unwrap().permissions().mode() & 0o777, 0o600);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha plaintext\n");
}

/// `init` refuses a repository that already tracks `*.secret` files: they
/// are plaintext in the index and history, and v3 would only appear to
/// protect them.
#[test]
fn init_refuses_secrets_already_tracked_in_plaintext() {
    let scratch = Scratch::new("pretracked");
    let repo = scratch.root.join("repo");
    fs::create_dir(&repo).unwrap();
    run(&repo, "git", &["init", "-q"], None);
    run(&repo, "git", &["config", "user.name", "Example"], None);
    run(&repo, "git", &["config", "user.email", "example@example.test"], None);
    fs::write(repo.join("old.secret"), b"PLAINTEXT IN HISTORY\n").unwrap();
    run(&repo, "git", &["add", "old.secret"], None);
    let err = run_fails(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
    assert!(err.contains("old.secret") && err.contains("already tracked"), "{err}");
    run(&repo, "git", &["commit", "-qm", "plaintext secret"], None);
    run(&repo, "git", &["rm", "-q", "--cached", "old.secret"], None);
    let err = run_fails(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
    assert!(err.contains("old.secret"), "{err}");
    assert!(!repo.join(".transcrypt").exists());
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

unsafe fn libc_fcntl_clear_cloexec(fd: i32) {
    extern "C" { fn fcntl(fd: i32, cmd: i32, ...) -> i32; }
    const F_SETFD: i32 = 2;
    fcntl(fd, F_SETFD, 0);
}

/// Editor and merge copies of secrets (`a.secret~`, `.a.secret.swp`,
/// `a.secret.orig`) are plaintext but not protected: they are ignored
/// locally, reported by status, and refused by the push audit.
#[test]
fn editor_and_merge_copies_of_secrets_are_caught() {
    let mut scratch = Scratch::new("copies");
    let repo = scratch.repo("repo");
    for name in ["a.secret~", "dir/.b.secret.swp", "a.secret.orig"] {
        fs::write(repo.join(name), b"PLAINTEXT COPY\n").unwrap();
    }
    // Ignored by `git add -A` in an unlocked checkout.
    run(&repo, "git", &["add", "-A"], None);
    assert!(run(&repo, "git", &["diff", "--cached", "--name-only"], None).is_empty());
    // Reported by status even when force-added, and refused by audit.
    run(&repo, "git", &["add", "-f", "a.secret.orig"], None);
    let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    assert!(status.contains("a.secret.orig is NOT encrypted"), "{status}");
    let err = run_fails(&repo, "git", &["commit", "-qm", "blocked by pre-commit"], None);
    assert!(err.contains("a.secret.orig"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "backup copy"], None);
    let err = run_fails(&repo, bin(), &["audit"], None);
    assert!(err.contains("a.secret.orig") && err.contains("copy of a secret"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    for name in ["a.secret~", "dir/.b.secret.swp", "a.secret.orig"] {
        let _ = fs::remove_file(repo.join(name));
    }
}
