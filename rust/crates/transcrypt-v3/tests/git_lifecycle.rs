//! End-to-end Git lifecycle. No Bash and no legacy crypto paths.
mod common;
use common::*;
use std::{fs, path::Path};

/// Unlocked means exactly one private key file in a private directory, and
/// no agent; locked means no key file.
fn assert_unlocked(root: &Path, expected: bool) {
    use std::os::unix::fs::PermissionsExt;
    let dir = root.join(".git/transcrypt-v3");
    let key = dir.join("key");
    if expected {
        let meta = fs::symlink_metadata(&key).expect("unlocked checkout must store its key");
        assert!(meta.file_type().is_file() && meta.len() == 55 + 64,
            "the key file holds the public config it unlocks and the 64-byte derived key");
        assert_eq!(meta.permissions().mode() & 0o077, 0, "key file must be private");
        assert_eq!(fs::metadata(&dir).unwrap().permissions().mode() & 0o077, 0);
        let items: Vec<_> = fs::read_dir(&dir).unwrap().map(|f| f.unwrap().file_name()).collect();
        assert_eq!(items, [std::ffi::OsString::from("key")], "nothing else in the credential directory");
    } else {
        assert!(!key.exists(), "the key must be forgotten while locked");
    }
    assert!(!dir.join("session.sock").exists(), "no agent in the default mode");
}

#[test]
fn git_init_commit_clone_unlock_hydrate_commit_lock_reunlock() {
    let mut scratch = Scratch::new("lifecycle");
    let source = scratch.git_repo("source");
    let (bin, pass) = (bin(), PASS);
    run(&source, bin, &["init", "--password-stdin", "*.secret"], Some(pass));
    assert_unlocked(&source, true);
    // The passphrase itself is stored nowhere.
    for file in ["config", "transcrypt-v3/key"] {
        let bytes = fs::read(source.join(".git").join(file)).unwrap();
        assert!(!bytes.windows(20).any(|w| w == &pass[..20]), "passphrase found in .git/{file}");
    }
    fs::write(source.join("account.secret"), b"private content\n").unwrap();
    fs::write(source.join("ledger.secret"), b"ledger content\n").unwrap();
    run(&source, "git", &["add", "account.secret", "ledger.secret"], None);
    run(&source, "git", &["commit", "-qm", "private data"], None);
    let object = run(&source, "git", &["show", "HEAD:account.secret"], None);
    assert!(is_record(&object));
    assert!(!object.windows(7).any(|w| w == b"private"));
    let ledger_object = run(&source, "git", &["show", "HEAD:ledger.secret"], None);
    // A local .git/info/attributes override is the user's choice, but
    // doctor reports it as missing protection.
    let info_attrs = source.join(".git/info/attributes");
    fs::write(&info_attrs, b"*.secret -filter\n").unwrap();
    run_fails(&source, bin, &["doctor"], None);
    fs::remove_file(&info_attrs).unwrap();
    run(&source, bin, &["verify-index"], None);
    // Selection follows Git's attribute rules, nested files included: a
    // nested staged .gitattributes protecting another name is honored.
    fs::create_dir(source.join("nested")).unwrap();
    fs::write(source.join("nested/.gitattributes"), b"invoice.txt transcrypt\n").unwrap();
    fs::write(source.join("nested/invoice.txt"), b"nested protection\n").unwrap();
    run(&source, "git", &["add", "nested"], None);
    assert!(run(&source, "git", &["show", ":nested/invoice.txt"], None).starts_with(b"TV3F\0\x01"));
    run(&source, bin, &["verify-index"], None);
    run(&source, "git", &["reset", "-q", "--", "nested"], None);
    fs::remove_dir_all(source.join("nested")).unwrap();
    run(&source, bin, &["verify-index"], None);
    let clone = scratch.clone("source", "clone");
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), object);
    assert_eq!(fs::read(clone.join("ledger.secret")).unwrap(), ledger_object);
    assert_unlocked(&clone, false);
    run_fails(&clone, bin, &["unlock", "--password-stdin"], Some(b"wrong password with enough characters\n"));
    assert_unlocked(&clone, false);
    run(&clone, bin, &["unlock", "--password-stdin", "--no-hydrate"], Some(pass));
    assert_unlocked(&clone, true);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), object, "--no-hydrate keeps ciphertext");
    // Altered but correctly sized public metadata is not authenticated by
    // the stored key: nothing is encrypted or decrypted under it.
    let metadata_path = clone.join(".transcrypt/config");
    let authentic_metadata = fs::read(&metadata_path).unwrap();
    let mut altered_metadata = authentic_metadata.clone();
    altered_metadata[8] ^= 1;
    fs::write(&metadata_path, altered_metadata).unwrap();
    run_fails(&clone, bin, &["clean", "account.secret"], Some(b"must not encrypt under changed metadata"));
    run_fails(&clone, bin, &["hydrate"], None);
    fs::write(&metadata_path, authentic_metadata).unwrap();
    // Hydrate replaces only authentic records. Unexpected local bytes in
    // another protected file are never overwritten (nor staged).
    fs::write(clone.join("ledger.secret"), b"unexpected local worktree data\n").unwrap();
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"private content\n");
    assert_eq!(fs::read(clone.join("ledger.secret")).unwrap(), b"unexpected local worktree data\n");
    assert_eq!(run(&clone, "git", &["diff", "--cached", "--name-only"], None), b"");
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
    fs::write(clone.join("account.secret"), b"updated secret\n").unwrap();
    run(&clone, "git", &["add", "account.secret"], None);
    run(&clone, "git", &["commit", "-qm", "update secret"], None);
    fs::write(clone.join("untracked.secret"), b"untracked plaintext\n").unwrap();
    run_fails(&clone, bin, &["lock"], None);
    assert_unlocked(&clone, true);
    fs::remove_file(clone.join("untracked.secret")).unwrap();
    run(&clone, bin, &["lock"], None);
    assert_unlocked(&clone, false);
    let locked = fs::read(clone.join("account.secret")).unwrap();
    assert_eq!(locked, run(&clone, "git", &["show", "HEAD:account.secret"], None));
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    assert_unlocked(&clone, true);
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join("account.secret")).unwrap(), b"updated secret\n");
    // A direct index write bypasses clean: the pre-commit hook encrypts the
    // staged plaintext, so the commit still holds only ciphertext.
    let forged_oid = String::from_utf8(run(
        &clone, "git", &["hash-object", "-w", "--stdin"], Some(b"STAGED PLAINTEXT\n"),
    )).unwrap();
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", forged_oid.trim(), "account.secret"], None);
    run(&clone, "git", &["commit", "-qm", "plaintext staged around the filter"], None);
    let committed = run(&clone, "git", &["show", "HEAD:account.secret"], None);
    assert!(is_record(&committed));
    assert_eq!(run(&clone, bin, &["smudge", "account.secret"], Some(&committed)), b"STAGED PLAINTEXT\n");
    // A record moved to another path in a commit is never re-encrypted for
    // it: the hook refuses, it does not launder the move.
    run(&clone, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&clone, "git", &["update-index", "--cacheinfo", "100644", ledger_oid.trim(), "account.secret"], None);
    run(&clone, "git", &["commit", "-q", "--no-verify", "-m", "hostile move"], None);
    run_fails(&clone, bin, &["verify-index"], None);
    fs::write(clone.join("README"), b"public edit\n").unwrap();
    run(&clone, "git", &["add", "README"], None);
    run_fails(&clone, "git", &["commit", "-qm", "must not launder the moved record"], None);
    run(&clone, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&source, bin, &["lock"], None);
    assert_unlocked(&source, false);
    run(&clone, bin, &["lock"], None);
    assert_unlocked(&clone, false);
}

#[test]
fn git_non_utf8_path_survives_filter_agent_commit_clone_and_hydration() {
    use std::os::unix::ffi::OsStringExt;
    let mut scratch = Scratch::new("raw-path");
    let source = scratch.git_repo("source");
    let (bin, pass) = (bin(), PASS);
    let name = std::ffi::OsString::from_vec(b"odd \xff'\nname.secret".to_vec());
    let payload = b"secret with a binary Git path\x00\xff";
    run(&source, bin, &["init", "--password-stdin", "*.secret"], Some(pass));
    fs::write(source.join(&name), payload).unwrap();
    // Git invokes the configured `%f` filter with the exact path byte string,
    // even though this path is neither UTF-8 nor shell-identifier-safe.
    run(&source, "git", &["add", "-A"], None);
    run(&source, "git", &["commit", "-qm", "raw-path encrypted record"], None);
    let index = run(&source, "git", &["ls-files", "-z"], None);
    assert!(index.split(|b| *b == 0).any(|part| part == b"odd \xff'\nname.secret"));
    let clone = scratch.clone("source", "clone");
    let committed_ciphertext = fs::read(clone.join(&name)).unwrap();
    assert!(is_record(&committed_ciphertext));
    assert_ne!(committed_ciphertext, payload);
    run(&clone, bin, &["unlock", "--password-stdin"], Some(pass));
    run(&clone, bin, &["hydrate"], None);
    assert_eq!(fs::read(clone.join(&name)).unwrap(), payload);
    run(&clone, bin, &["verify-index"], None);
    run(&clone, bin, &["lock"], None);
    assert_eq!(fs::read(clone.join(&name)).unwrap(), committed_ciphertext);
}
