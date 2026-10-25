//! End-to-end Git lifecycle. No Bash and no legacy crypto paths.
use std::os::unix::fs::FileTypeExt;
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

fn assert_in_memory_session(root: &Path, expected: bool) {
    let dir = root.join(".git/transcrypt-v3");
    assert!(!dir.join("key").exists(), "v3 derived key must never be persisted");
    let sock = dir.join("session.sock");
    if expected {
        let meta = fs::symlink_metadata(&sock).expect("session must be live");
        assert!(meta.file_type().is_socket(), "credential endpoint must be a socket");
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(meta.permissions().mode() & 0o077, 0);
        let items: Vec<_> = fs::read_dir(&dir).unwrap().map(|f| f.unwrap().file_name()).collect();
        assert_eq!(items.len(), 1, "no persistent files in credential directory");
        assert_eq!(items[0], std::ffi::OsString::from("session.sock"));
    } else {
        assert!(!sock.exists(), "credential socket must not exist while locked");
    }
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
    assert_in_memory_session(&source, true);
    fs::write(source.join("account.secret"), b"private content\n").unwrap();
    fs::write(source.join("ledger.secret"), b"ledger content\n").unwrap();
    run(&source, "git", &["add", "account.secret", "ledger.secret"], None);
    run(&source, "git", &["commit", "-qm", "private data"], None);
    let object = run(&source, "git", &["show", "HEAD:account.secret"], None);
    assert!(object.starts_with(b"TV3F\0\x01"));
    assert!(!object.windows(7).any(|w| w == b"private"));
    let ledger_object = run(&source, "git", &["show", "HEAD:ledger.secret"], None);
    // The staged root policy can be correct while .git/info/attributes
    // silently overrides the effective filter. Refuse that checkout.
    let info_attrs = source.join(".git/info/attributes");
    fs::write(&info_attrs, b"*.secret -filter\n").unwrap();
    run_fails(&source, bin, &["verify-index"], None);
    run_fails(&source, bin, &["lock"], None);
    assert_in_memory_session(&source, true);
    fs::remove_file(&info_attrs).unwrap();
    run(&source, bin, &["verify-index"], None);
    // A nested staged attributes file also takes precedence, even if the
    // worktree .gitattributes subsequently differs from the staged policy.
    fs::create_dir(source.join("nested")).unwrap();
    fs::write(source.join("nested/.gitattributes"), b"*.secret -filter\n").unwrap();
    fs::write(source.join("nested/invoice.secret"), b"must never be staged plaintext\n").unwrap();
    run(&source, "git", &["add", "nested/.gitattributes", "nested/invoice.secret"], None);
    run_fails(&source, bin, &["verify-index"], None);
    run(&source, "git", &["reset", "-q", "--", "nested/.gitattributes", "nested/invoice.secret"], None);
    fs::remove_dir_all(source.join("nested")).unwrap();
    run(&source, bin, &["verify-index"], None);
    run(&temp, "git", &["clone", "-q", "source", "clone"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), object);
    assert_eq!(fs::read(clone.join("ledger.secret")).unwrap(), ledger_object);
    assert_in_memory_session(&clone, false);
    run_fails(&clone, bin, &["unlock", "--password-stdin"], Some(b"wrong password with enough characters\n"));
    assert_in_memory_session(&clone, false);
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    assert_in_memory_session(&clone, true);
    // Altered but correctly sized public metadata must not be accepted by
    // the agent that authenticated the original bytes at unlock.
    let metadata_path = clone.join(".transcrypt/config");
    let authentic_metadata = fs::read(&metadata_path).unwrap();
    let mut altered_metadata = authentic_metadata.clone();
    altered_metadata[8] ^= 1;
    fs::write(&metadata_path, altered_metadata).unwrap();
    run_fails(&clone, bin, &["clean", "account.secret"], Some(b"must not encrypt under changed metadata"));
    fs::write(&metadata_path, authentic_metadata).unwrap();
    // If any protected path is unexpected, preflight must refuse to touch
    // every path. Previously restoring one at a time risked partial writes.
    fs::write(clone.join("ledger.secret"), b"unexpected local worktree data\n").unwrap();
    run_fails(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), object);
    fs::write(clone.join("ledger.secret"), &ledger_object).unwrap();
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"private content\n");
    assert_eq!(fs::read(clone.join("ledger.secret")).unwrap(), b"ledger content\n");
    // Simulate an interrupted multi-file hydration: one path has reverted to
    // ciphertext, while the other has already been hydrated. Retrying must
    // complete the missing path and preserve the previously hydrated one.
    fs::write(clone.join("ledger.secret"), &ledger_object).unwrap();
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"private content\n");
    assert_eq!(fs::read(clone.join("ledger.secret")).unwrap(), b"ledger content\n");
    // Fully repeated hydration must also succeed. No ciphertext is ever
    // passed to Git restore's implicit clean-filter refresh.
    run(&clone, bin, &["hydrate"], None);
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    // Both objects are valid AES-SIV ciphertext, but for DIFFERENT paths.
    // Swapping their staged blobs must be rejected before any plaintext
    // is produced or the working tree is changed.
    let account_oid = String::from_utf8(run(
        &clone, "git", &["rev-parse", ":account.secret"], None,
    )).unwrap();
    let ledger_oid = String::from_utf8(run(
        &clone, "git", &["rev-parse", ":ledger.secret"], None,
    )).unwrap();
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", ledger_oid.trim(), "account.secret"], None);
    run_fails(&clone, bin, &["verify-index"], None);
    run_fails(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"private content\n");
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", account_oid.trim(), "account.secret"], None);
    run(&clone, bin, &["verify-index"], None);
    // The lower-level filter must also reject valid ciphertext with a
    // mismatched Git path, even if an attacker invokes it directly.
    run_fails(&clone, bin, &["smudge", "ledger.secret"], Some(&object));
    run_fails(&clone, bin, &["clean"], Some(b"missing path"));
    // Hydration must use the exact staged ciphertext. HEAD deliberately still
    // contains the original secret, while the index contains a newer one.
    let staged_blob = run(&clone, bin, &["clean", "account.secret"], Some(b"staged snapshot\n"));
    let staged_id = String::from_utf8(run(
        &clone, "git", &["hash-object", "-w", "--stdin"], Some(&staged_blob),
    )).unwrap();
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", staged_id.trim(), "account.secret"], None);
    fs::write(clone.join("account.secret"), &staged_blob).unwrap();
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"staged snapshot\n");
    // Undo the staged-only experiment before continuing the normal lifecycle.
    run(&clone, "git", &["reset", "-q", "HEAD", "--", "account.secret"], None);
    fs::write(clone.join("account.secret"), b"private content\n").unwrap();
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    run(&clone, "git", &["config", "user.name", "Example"], None);
    run(&clone, "git", &["config", "user.email", "example@example.test"], None);
    fs::write(clone.join("account.secret"), b"updated secret\n").unwrap();
    run(&clone, "git", &["add", "account.secret"], None);
    run(&clone, "git", &["commit", "-qm", "update secret"], None);
    fs::write(clone.join("untracked.secret"), b"untracked plaintext\n").unwrap();
    run_fails(&clone, bin, &["lock"], None);
    assert_in_memory_session(&clone, true);
    fs::remove_file(clone.join("untracked.secret")).unwrap();
    run(&clone, bin, &["lock"], None);
    assert_in_memory_session(&clone, false);
    let locked = fs::read(clone.join("account.secret")).unwrap();
    assert_eq!(locked, run(&clone, "git", &["show", "HEAD:account.secret"], None));
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    assert_in_memory_session(&clone, true);
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"updated secret\n");
    // A direct index write bypasses clean. The hook must still block it.
    let forged_oid = String::from_utf8(run(
        &clone, "git", &["hash-object", "-w", "--stdin"], Some(b"STAGED PLAINTEXT\n"),
    )).unwrap();
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", forged_oid.trim(), "account.secret"], None);
    run_fails(&clone, "git", &["commit", "-qm", "try forged ciphertext"], None);
    // Do not leak background agent processes when this integration test ends.
    run(&source, bin, &["lock"], None);
    assert_in_memory_session(&source, false);
    // The clone has a forged staged object, so abort the test without
    // asking lock to overwrite a file whose staged ciphertext is invalid.
    // Restore the authenticated index before stopping the agent.
    run(&clone, "git", &["reset", "-q", "HEAD", "--", "account.secret"], None);
    run(&clone, bin, &["lock"], None);
    assert_in_memory_session(&clone, false);
    let _ = fs::remove_dir_all(&temp);
}


#[test]
fn git_non_utf8_path_survives_filter_agent_commit_clone_and_hydration() {
    use std::os::unix::ffi::OsStringExt;
    let temp = std::env::temp_dir().join(format!(
        "transcrypt-v3-raw-path-{}-{}", std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    fs::create_dir(&temp).unwrap();
    let source = temp.join("source");
    let clone = temp.join("clone");
    fs::create_dir(&source).unwrap();
    let bin = env!("CARGO_BIN_EXE_transcrypt-v3");
    let pass = b"long correct horse battery staple test passphrase\n";
    let name = std::ffi::OsString::from_vec(b"odd \xff'\nname.secret".to_vec());
    let payload = b"secret with a binary Git path\x00\xff";
    run(&source, "git", &["init", "-q"], None);
    run(&source, "git", &["config", "user.name", "Example"], None);
    run(&source, "git", &["config", "user.email", "example@example.test"], None);
    fs::write(source.join("README"), b"public\n").unwrap();
    run(&source, "git", &["add", "README"], None);
    run(&source, "git", &["commit", "-qm", "seed"], None);
    run(&source, bin, &["init", "--password-stdin"], Some(pass));
    fs::write(source.join(&name), payload).unwrap();
    // Git invokes the configured `%f` filter with the exact path byte string,
    // even though this path is neither UTF-8 nor shell-identifier-safe.
    run(&source, "git", &["add", "-A"], None);
    run(&source, "git", &["commit", "-qm", "raw-path encrypted record"], None);
    let index = run(&source, "git", &["ls-files", "-z"], None);
    assert!(index.split(|b| *b == 0).any(|part| part == b"odd \xff'\nname.secret"));
    run(&temp, "git", &["clone", "-q", "source", "clone"], None);
    let committed_ciphertext = fs::read(clone.join(&name)).unwrap();
    assert!(committed_ciphertext.starts_with(b"TV3F\0\x01"));
    assert_ne!(committed_ciphertext, payload);
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join(&name)).unwrap(), payload);
    run(&clone, bin, &["verify-index"], None);
    run(&clone, bin, &["lock"], None);
    assert_eq!(fs::read(clone.join(&name)).unwrap(), committed_ciphertext);
    run(&source, bin, &["lock"], None);
    let _ = fs::remove_dir_all(&temp);
}
