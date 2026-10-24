//! End-to-end Git lifecycle. No Bash and no legacy crypto paths.
use std::{fs, io::Write, path::Path, process::{Command, Stdio}};

fn run(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) -> Vec<u8> {
    let mut command = Command::new(name);
    command.args(args).current_dir(dir).stdout(Stdio::piped()).stderr(Stdio::piped());
    if input.is_some() { command.stdin(Stdio::piped()); }
    let mut child = command.spawn().unwrap();
    if let Some(value) = input {
        child.stdin.take().unwrap().write_all(value).unwrap();
    }
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "{name} {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
    out.stdout
}

fn run_fails(dir: &Path, name: &str, args: &[&str], input: Option<&[u8]>) {
    let mut command = Command::new(name);
    command.args(args).current_dir(dir).stdout(Stdio::piped()).stderr(Stdio::piped());
    if input.is_some() { command.stdin(Stdio::piped()); }
    let mut child = command.spawn().unwrap();
    if let Some(value) = input { child.stdin.take().unwrap().write_all(value).unwrap(); }
    let out = child.wait_with_output().unwrap();
    assert!(!out.status.success(), "{name} {args:?} unexpectedly succeeded");
}

#[test]
fn git_init_commit_clone_unlock_hydrate_commit_lock_reunlock() {
    let temp = std::env::temp_dir().join(format!(
        "transcrypt-v3-lifecycle-{}-{}", std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    fs::create_dir(&temp).unwrap();
    let source = temp.join("source");
    let clone = temp.join("clone");
    fs::create_dir(&source).unwrap();
    let bin = env!("CARGO_BIN_EXE_transcrypt-v3");
    let pass = b"long correct horse battery staple test passphrase\n";
    run(&source, "git", &["init", "-q"], None);
    run(&source, "git", &["config", "user.name", "Example"], None);
    run(&source, "git", &["config", "user.email", "example@example.test"], None);
    fs::write(source.join("README"), b"public\n").unwrap();
    run(&source, "git", &["add", "README"], None);
    run(&source, "git", &["commit", "-qm", "seed"], None);
    run(&source, bin, &["init", "--password-stdin"], Some(pass));
    fs::write(source.join("account.secret"), b"private content\n").unwrap();
    run(&source, "git", &["add", "account.secret"], None);
    run(&source, "git", &["commit", "-qm", "private data"], None);
    let object = run(&source, "git", &["show", "HEAD:account.secret"], None);
    assert!(object.starts_with(b"TV3F\0\x01"));
    assert!(!object.windows(7).any(|w| w == b"private"));
    run(&temp, "git", &["clone", "-q", "source", "clone"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), object);
    run_fails(&clone, bin, &["unlock", "--password-stdin"], Some(b"wrong password with enough characters\n"));
    assert!(!clone.join(".git/transcrypt-v3/key").exists());
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"private content\n");
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    run(&clone, "git", &["config", "user.name", "Example"], None);
    run(&clone, "git", &["config", "user.email", "example@example.test"], None);
    fs::write(clone.join("account.secret"), b"updated secret\n").unwrap();
    run(&clone, "git", &["add", "account.secret"], None);
    run(&clone, "git", &["commit", "-qm", "update secret"], None);
    fs::write(clone.join("untracked.secret"), b"untracked plaintext\n").unwrap();
    run_fails(&clone, bin, &["lock"], None);
    assert!(clone.join(".git/transcrypt-v3/key").exists());
    fs::remove_file(clone.join("untracked.secret")).unwrap();
    run(&clone, bin, &["lock"], None);
    assert!(!clone.join(".git/transcrypt-v3/key").exists());
    let locked = fs::read(clone.join("account.secret")).unwrap();
    assert_eq!(locked, run(&clone, "git", &["show", "HEAD:account.secret"], None));
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"updated secret\n");
    // A direct index write bypasses clean. The hook must still block it.
    let forged_oid = String::from_utf8(run(
        &clone, "git", &["hash-object", "-w", "--stdin"], Some(b"STAGED PLAINTEXT\n"),
    )).unwrap();
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", forged_oid.trim(), "account.secret"], None);
    run_fails(&clone, "git", &["commit", "-qm", "try forged ciphertext"], None);
    let _ = fs::remove_dir_all(&temp);
}
