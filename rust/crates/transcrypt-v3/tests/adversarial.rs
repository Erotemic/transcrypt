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
        (b'E', &config, b"a.secret", &record[..]),         // double encryption
        (b'P', &config, b"a.secret", &b""[..]),            // control op with a path
        (b'Q', &config, b"", &b""[..]),                    // unknown opcode
    ] {
        assert!(agent_request(&repo, op, cfg, path, body).is_err(), "accepted op {}", op as char);
    }
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
