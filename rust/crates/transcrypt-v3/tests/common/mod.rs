//! Helpers shared by the end-to-end tests: running Git and the binary, and
//! scratch repositories that are locked and removed when a test ends.
#![allow(dead_code)]
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::{fs, time::Duration};

pub const PASS: &[u8] = b"long correct horse battery staple test passphrase\n";

pub fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_transcrypt-v3")
}

pub fn exec(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> Output {
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

fn succeeded(name: &str, args: &[&str], out: &Output) {
    assert!(out.status.success(), "{name} {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
}

pub fn run(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> Vec<u8> {
    let out = exec(dir, name, args, input);
    succeeded(name, args, &out);
    out.stdout
}

/// Run and return stderr (where v3 reports what it did).
pub fn run_err(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> String {
    let out = exec(dir, name, args, input);
    succeeded(name, args, &out);
    String::from_utf8_lossy(&out.stderr).into_owned()
}

pub fn run_fails(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> String {
    let out = exec(dir, name, args, input);
    assert!(!out.status.success(), "{name} {args:?} unexpectedly succeeded");
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// `git add PATHS` and `git commit -qm MESSAGE`.
pub fn commit(repo: &Path, paths: &[&str], message: &str) {
    let mut add = vec!["add"];
    add.extend_from_slice(paths);
    run(repo, "git", &add, None);
    run(repo, "git", &["commit", "-qm", message], None);
}

/// `git add -A` and `git commit -qm MESSAGE`.
pub fn commit_all(repo: &Path, message: &str) {
    commit(repo, &["-A"], message);
}

pub fn staged(repo: &Path, path: &str) -> Vec<u8> {
    run(repo, "git", &["show", &format!(":{path}")], None)
}

pub fn committed(repo: &Path, path: &str) -> Vec<u8> {
    run(repo, "git", &["show", &format!("HEAD:{path}")], None)
}

/// Bytes from hexadecimal text.
pub fn hex(value: &str) -> Vec<u8> {
    assert_eq!(value.len() % 2, 0);
    value.as_bytes().chunks(2).map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap()).collect()
}

pub fn is_record(bytes: &[u8]) -> bool {
    bytes.starts_with(b"TV3F\0\x01")
}

pub fn socket(repo: &Path) -> PathBuf {
    repo.join(".git/transcrypt-v3/session.sock")
}

/// Unlock with `PASS`, storing the key.
pub fn unlock(repo: &Path) {
    run(repo, bin(), &["unlock", "--password-stdin"], Some(PASS));
}

/// Switch a repository to the private mode: key in an in-memory agent,
/// decrypted files private to this user.
pub fn private(repo: &Path) {
    run(repo, bin(), &["unlock", "--private", "--password-stdin"], Some(PASS));
    assert!(socket(repo).exists() && !repo.join(".git/transcrypt-v3/key").exists());
}

/// Whether a key is available (stored, or held by the private agent).
pub fn unlocked(repo: &Path) -> bool {
    repo.join(".git/transcrypt-v3/key").exists() || socket(repo).exists()
}

/// Speak the agent's framing directly, as a hostile same-UID client could.
pub fn agent_request(repo: &Path, op: u8, config: &[u8], path: &[u8], body: &[u8]) -> Result<Vec<u8>, String> {
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

/// A scratch directory, removed (every repository locked and any agent
/// stopped) when the test ends.
pub struct Scratch {
    pub root: PathBuf,
    pub repos: Vec<PathBuf>,
}

impl Scratch {
    pub fn new(tag: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "transcrypt-v3-{tag}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        Scratch { root, repos: Vec::new() }
    }

    /// Set a commit identity in `repo`.
    pub fn identify(repo: &Path) {
        run(repo, "git", &["config", "user.name", "Example"], None);
        run(repo, "git", &["config", "user.email", "example@example.test"], None);
    }

    /// A Git repository with one public commit, not yet using v3.
    pub fn git_repo(&mut self, name: &str) -> PathBuf {
        let repo = self.root.join(name);
        fs::create_dir_all(&repo).unwrap();
        run(&repo, "git", &["init", "-q"], None);
        Self::identify(&repo);
        fs::write(repo.join("README"), b"public\n").unwrap();
        commit(&repo, &["README"], "seed");
        self.repos.push(repo.clone());
        repo
    }

    /// An initialized, unlocked v3 repository with two committed secrets.
    pub fn repo(&mut self, name: &str) -> PathBuf {
        let repo = self.git_repo(name);
        run(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
        fs::create_dir(repo.join("dir")).unwrap();
        fs::write(repo.join("a.secret"), b"alpha plaintext\n").unwrap();
        fs::write(repo.join("dir/b.secret"), b"beta plaintext\n").unwrap();
        commit_all(&repo, "secrets");
        repo
    }

    pub fn clone(&mut self, from: &str, name: &str) -> PathBuf {
        run(&self.root, "git", &["clone", "-q", from, name], None);
        let repo = self.root.join(name);
        Self::identify(&repo);
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
