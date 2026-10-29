//! Helpers shared by the end-to-end tests: running Git and the binary, and
//! scratch repositories that are locked and removed when a test ends.
#![allow(dead_code)]
use std::io::{Read, Write};
#[cfg(unix)]
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
        // A command refused before it reads its input closes the pipe; its
        // exit status, not this write, is what the test checks.
        match child.stdin.take().unwrap().write_all(value) {
            Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => {},
            other => other.unwrap(),
        }
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

/// The agent's socket client and listener on Windows, which std lacks:
/// the adapter's own (only the transport; privacy is checked with icacls).
#[cfg(windows)]
#[allow(dead_code, unused_imports)]
#[path = "../../src/os_windows.rs"]
pub mod os;
#[cfg(windows)]
#[allow(unused_imports)]
pub(crate) use os::{Listener as UnixListener, Stream as UnixStream};

/// Speak the agent's framing directly, as a hostile same-UID client could.
pub fn agent_request(repo: &Path, op: u8, config: &[u8], path: &[u8], body: &[u8]) -> Result<Vec<u8>, String> {
    let mut stream = UnixStream::connect(socket(repo)).map_err(|e| e.to_string())?;
    #[cfg(unix)]
    stream.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    #[cfg(windows)]
    os::set_timeouts(&stream, Duration::from_secs(30)).unwrap();
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
        // Short paths under /tmp: the tests reach the agent's socket by its
        // absolute path, and a socket address is at most 104 bytes on macOS
        // and the BSDs, which macOS's per-user $TMPDIR alone nearly fills.
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let base = if Path::new("/tmp").is_dir() { PathBuf::from("/tmp") } else { std::env::temp_dir() };
        loop {
            let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let root = base.join(format!("tv3-{tag}-{}-{n}", std::process::id()));
            match fs::create_dir(&root) {
                Ok(()) => return Scratch { root, repos: Vec::new() },
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("cannot create {}: {e}", root.display()),
            }
        }
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
        run(&repo, "git", &["init", "-q", "-b", "main"], None);
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

/// Make a directory private to this user, as v3 makes its own.
pub fn make_private_dir(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }
    #[cfg(windows)]
    icacls(path, &["/inheritance:r", "/grant:r", &format!("*{}:(OI)(CI)F", user_sid())]);
}

/// Make a file readable by other users.
pub fn make_public(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o644)).unwrap();
    }
    #[cfg(windows)]
    icacls(path, &["/grant", "*S-1-1-0:(R)"]);
}

/// Make a file executable (Git for Windows runs any hook file).
pub fn make_executable(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }
    #[cfg(windows)]
    let _ = path;
}

/// Whether only this user can open the file or directory: no group or other
/// permission on Unix; on Windows, as `icacls` lists it: nothing inherited,
/// and only this user granted access.
pub fn owner_only(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path).unwrap().permissions().mode() & 0o077 == 0
    }
    #[cfg(windows)]
    {
        let out = exec(path.parent().unwrap(), "icacls", &[path.to_str().unwrap()], None);
        assert!(out.status.success(), "icacls failed");
        let text = String::from_utf8_lossy(&out.stdout).into_owned();
        let me = user_name().to_lowercase();
        let entries: Vec<String> = text.lines().filter_map(|line| {
            let line = line.strip_prefix(path.to_str().unwrap()).unwrap_or(line).trim();
            line.contains(":(").then(|| line.to_lowercase())
        }).collect();
        !entries.is_empty() && entries.iter().all(|e| e.starts_with(&format!("{me}:(")) && !e.contains("(i)"))
    }
}

/// A symlink at `link` to `target` (on Windows, a junction for a directory,
/// which needs no privilege).
pub fn symlink(target: &Path, link: &Path) {
    #[cfg(unix)]
    std::os::unix::fs::symlink(target, link).unwrap();
    #[cfg(windows)]
    {
        let resolved = link.parent().unwrap().join(target);
        if resolved.is_dir() {
            let out = exec(link.parent().unwrap(), "cmd", &["/c", "mklink", "/J", link.to_str().unwrap(),
                resolved.to_str().unwrap()], None);
            assert!(out.status.success(), "mklink /J failed: {}", String::from_utf8_lossy(&out.stderr));
        } else {
            std::os::windows::fs::symlink_file(target, link).unwrap();
        }
    }
}

/// Remove a symlink or junction (a junction is a directory on Windows).
pub fn remove_link(link: &Path) {
    if fs::remove_file(link).is_err() { fs::remove_dir(link).unwrap(); }
}

#[cfg(windows)]
fn icacls(path: &Path, args: &[&str]) {
    let mut all = vec![path.to_str().unwrap()];
    all.extend_from_slice(args);
    let out = exec(path.parent().unwrap(), "icacls", &all, None);
    assert!(out.status.success(), "icacls {args:?} failed: {}", String::from_utf8_lossy(&out.stdout));
}

/// `DOMAIN\user` and the SID of this user, as `whoami` reports them.
#[cfg(windows)]
fn whoami() -> (String, String) {
    let out = exec(Path::new("."), "whoami", &["/user", "/fo", "csv", "/nh"], None);
    let text = String::from_utf8_lossy(&out.stdout).trim().replace('"', "");
    let (name, sid) = text.split_once(',').unwrap();
    (name.to_owned(), sid.to_owned())
}

#[cfg(windows)]
fn user_name() -> String { whoami().0 }

#[cfg(windows)]
fn user_sid() -> String { whoami().1 }
