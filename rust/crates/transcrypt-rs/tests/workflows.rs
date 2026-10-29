//! Everyday workflows with arbitrary protected-file patterns and the
//! default stored-key unlock, against real Git: selection by
//! `.gitattributes`, renames, unusual names, credential modes, policy
//! changes and the reviewed `rekey` symlink attack.
mod common;
use common::*;
#[cfg(unix)]
use std::os::unix::{ffi::OsStringExt, fs::PermissionsExt};
use std::path::PathBuf;
#[cfg(unix)]
use std::{io::Write, process::{Command, Stdio}};
use std::{ffi::OsString, fs, time::{Duration, Instant}};
use transcrypt_rs::KEY_SIZE;
use transcrypt_v3_core::{KEY_FILE_LEN, REGULAR_MODE};

const NEW: &[u8] = b"a completely different long passphrase\n";

/// The acceptance criterion of the product charter: `.env`, a file in a
/// directory, a whole directory, a custom pattern, names with spaces,
/// quotes, newlines and non-UTF-8 bytes, an executable, a nested
/// `.gitattributes` and an exclusion all get exactly the guarantees the
/// old `*.secret` files had, through ordinary Git commands.
#[test]
fn arbitrary_patterns_protect_exactly_the_selected_files() {
    let mut scratch = Scratch::new("patterns");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", ".env", "config/production.yaml", "private/**", "*.key",
        "name with space.txt"], Some(PASS));
    fs::create_dir_all(repo.join("config")).unwrap();
    fs::create_dir_all(repo.join("private/deep/er")).unwrap();
    fs::create_dir_all(repo.join("nested")).unwrap();
    // Not UTF-8, with a quote and a newline; Windows names allow neither,
    // and macOS (APFS) only UTF-8.
    #[cfg(all(unix, not(target_os = "macos")))]
    let odd = OsString::from_vec(b"private/odd \xff'\"\nname".to_vec());
    #[cfg(target_os = "macos")]
    let odd = OsString::from("private/odd \u{e9}'\"\nname");
    #[cfg(windows)]
    let odd = OsString::from("private/odd \u{e9}'% name");
    let files: Vec<(PathBuf, &[u8])> = vec![
        (".env".into(), b"API_KEY=hunter2\n"),
        ("config/production.yaml".into(), b"password: swordfish\n"),
        ("private/deep/er/notes.md".into(), b"deep private notes\n"),
        ("private/run.sh".into(), b"#!/bin/sh\necho private\n"),
        ("server.key".into(), b"-----BEGIN KEY-----\n"),
        ("name with space.txt".into(), b"spaced secret\n"),
        (odd.clone().into(), b"odd secret\x00\xff"),
        ("nested/local.cfg".into(), b"nested secret\n"),
    ];
    for (path, content) in &files {
        fs::write(repo.join(path), content).unwrap();
    }
    #[cfg(unix)]
    fs::set_permissions(repo.join("private/run.sh"), fs::Permissions::from_mode(EXECUTABLE_FILE)).unwrap();
    // A nested policy, and a public file excluded from a protected directory.
    fs::write(repo.join("nested/.gitattributes"), b"local.cfg transcrypt\n").unwrap();
    fs::write(repo.join("private/PUBLIC.md"), b"public readme\n").unwrap();
    let mut attributes = fs::read(repo.join(".gitattributes")).unwrap();
    attributes.extend_from_slice(b"private/PUBLIC.md -filter -diff -merge\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    fs::write(repo.join("config/development.yaml"), b"public config\n").unwrap();
    commit_all(&repo, "protected files");
    let listing = run(&repo, "git", &["ls-files", "-z", "-s"], None);
    #[cfg(unix)]
    assert!(listing.split(|b| *b == 0).any(|e| e.starts_with(&transcrypt_v3_core::EXECUTABLE_MODE) && e.ends_with(b"private/run.sh")));
    // An index record is `<mode> <oid> 0\t<path>`; a leak probe is the
    // first bytes of a file's content.
    const OID_START: usize = REGULAR_MODE.len() + 1;
    const STAGE_FIELD_LEN: usize = b" 0".len();
    const LEAK_PROBE: usize = 6;
    for (path, content) in &files {
        let name = path.to_str().map(str::to_owned).unwrap_or_else(|| String::from_utf8_lossy(odd.as_encoded_bytes()).into_owned());
        let blob = match path.to_str() {
            Some(p) => committed(&repo, p),
            None => {
                let entry = listing.split(|b| *b == 0).find(|e| e.ends_with(b"odd \xff'\"\nname")).unwrap();
                let tab = entry.iter().position(|b| *b == b'\t').unwrap();
                let oid = std::str::from_utf8(&entry[OID_START..tab - STAGE_FIELD_LEN]).unwrap();
                run(&repo, "git", &["cat-file", "blob", oid], None)
            },
        };
        assert!(is_record(&blob), "{name} committed unencrypted");
        let probe = &content[..content.len().min(LEAK_PROBE)];
        assert!(!blob.windows(probe.len()).any(|w| w == probe), "{name} leaks");
        assert_eq!(fs::read(repo.join(path)).unwrap(), *content, "{name} worktree");
    }
    for public in ["README", "private/PUBLIC.md", "config/development.yaml", ".gitattributes", "nested/.gitattributes"] {
        assert!(!is_record(&committed(&repo, public)), "{public} must stay public");
    }
    let out = String::from_utf8(run(&repo, bin(), &["audit"], None)).unwrap();
    assert!(out.contains("8 protected record(s) checked, all authenticated"), "{out}");
    // A fresh clone sees ciphertext until it unlocks, then the same files.
    let clone = scratch.clone("repo", "clone");
    assert!(is_record(&fs::read(clone.join(".env")).unwrap()));
    unlock(&clone);
    for (path, content) in &files {
        assert_eq!(fs::read(clone.join(path)).unwrap(), *content);
    }
    #[cfg(unix)]
    assert_eq!(fs::metadata(clone.join("private/run.sh")).unwrap().permissions().mode() & modes::EXECUTE_BITS,
        modes::EXECUTE_BITS, "an executable protected file stays executable");
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    // Lock restores ciphertext (keeping modes), and unlock decrypts again.
    run(&clone, bin(), &["lock"], None);
    assert!(is_record(&fs::read(clone.join("private/run.sh")).unwrap()));
    #[cfg(unix)]
    assert_eq!(fs::metadata(clone.join("private/run.sh")).unwrap().permissions().mode() & modes::EXECUTE_BITS,
        modes::EXECUTE_BITS);
    assert!(run(&clone, "git", &["status", "--porcelain"], None).is_empty());
    unlock(&clone);
    assert_eq!(fs::read(clone.join(&odd)).unwrap(), b"odd secret\x00\xff");
}

/// Unlock once: the key is stored (not the passphrase), no process keeps
/// running, and Git works in later processes without prompting. Plaintext
/// has ordinary permissions. Lock forgets the key.
#[test]
fn stored_key_unlock_needs_no_agent_and_follows_the_umask() {
    let mut scratch = Scratch::new("stored");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", ".env"], Some(PASS));
    fs::write(repo.join(".env"), b"one\n").unwrap();
    commit(&repo, &[".env"], "env");
    let key = repo.join(".git/transcrypt-v3/key");
    assert!(owner_only(&key));
    assert!(!repo.join(".git/transcrypt-v3/session.sock").exists(), "no agent in the default mode");
    assert!(!fs::read(repo.join(".git/config")).unwrap().windows(PASS_EXCERPT).any(|w| w == &PASS[..PASS_EXCERPT]));
    // Every later Git command finds the key by itself.
    run(&repo, "git", &["checkout", "-q", "-b", "side"], None);
    fs::write(repo.join(".env"), b"two\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "two"], None);
    let script = "umask 022 && exec git checkout -q -";
    run(&repo, "sh", &["-c", script], None);
    assert_eq!(fs::read(repo.join(".env")).unwrap(), b"one\n", "checkout decrypts directly");
    #[cfg(unix)]
    assert_eq!(fs::metadata(repo.join(".env")).unwrap().permissions().mode() & modes::PERMISSION_BITS, PUBLIC_FILE,
        "plaintext follows the umask in the default mode");
    #[cfg(windows)]
    assert!(!owner_only(&repo.join(".env")), "plaintext has its directory's access in the default mode");
    let diff = String::from_utf8(run(&repo, "git", &["diff", "HEAD", "side", "--", ".env"], None)).unwrap();
    assert!(diff.contains("-one") && diff.contains("+two"), "{diff}");
    run(&repo, "git", &["merge", "-q", "side"], None);
    assert_eq!(fs::read(repo.join(".env")).unwrap(), b"two\n");
    run(&repo, bin(), &["lock"], None);
    assert!(!key.exists(), "lock forgets the key");
    assert!(is_record(&fs::read(repo.join(".env")).unwrap()));
    fs::write(repo.join("new.env"), b"x\n").unwrap();
    let err = run_fails(&repo, bin(), &["protect", "new.env"], None);
    assert!(err.contains("locked"), "{err}");
    fs::remove_file(repo.join("new.env")).unwrap();
}

/// Both credential modes produce byte-identical records: the mode changes
/// where the key waits, not the ciphertext.
#[test]
fn stored_and_private_modes_encrypt_identically() {
    let mut scratch = Scratch::new("modes");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.txt"], Some(PASS));
    let stored = run(&repo, bin(), &["clean", "a.txt"], Some(b"same input\n"));
    assert_eq!(run(&repo, bin(), &["smudge", "a.txt"], Some(&stored)), b"same input\n");
    run(&repo, bin(), &["unlock", "--private", "--password-stdin"], Some(PASS));
    assert!(!repo.join(".git/transcrypt-v3/key").exists());
    assert!(repo.join(".git/transcrypt-v3/session.sock").exists());
    let private = run(&repo, bin(), &["clean", "a.txt"], Some(b"same input\n"));
    assert!(is_record(&stored));
    assert_eq!(stored, private);
    // Private mode releases plaintext to Git only under a private umask (on
    // Windows never: hydrate writes it, owner-only).
    let smudge = format!("umask 077 && exec '{}' smudge a.txt", bin());
    let released: &[u8] = if cfg!(windows) { &stored } else { b"same input\n" };
    assert_eq!(run(&repo, "sh", &["-c", &smudge], Some(&stored)), released);
    let smudge = format!("umask 022 && exec '{}' smudge a.txt", bin());
    assert_eq!(run(&repo, "sh", &["-c", &smudge], Some(&stored)), stored);
    unlock(&repo);
    assert!(repo.join(".git/transcrypt-v3/key").exists());
    assert!(!repo.join(".git/transcrypt-v3/session.sock").exists(), "switching back stops the agent");
}

/// `git mv` keeps the blob, which is bound to the old path. The pre-commit
/// hook re-encrypts it for the new name, also for whole directories and for
/// moves from an unprotected name; a clone decrypts every result.
#[test]
fn renames_are_re_encrypted_for_their_new_path() {
    let mut scratch = Scratch::new("rename");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.secret", "vault/**"], Some(PASS));
    fs::create_dir_all(repo.join("dir")).unwrap();
    fs::write(repo.join("a.secret"), b"alpha\n").unwrap();
    fs::write(repo.join("dir/b.secret"), b"beta\n").unwrap();
    fs::write(repo.join("dir/c.secret"), b"gamma\n").unwrap();
    fs::write(repo.join("notes.txt"), b"was public\n").unwrap();
    commit_all(&repo, "files");
    run(&repo, "git", &["mv", "a.secret", "renamed.secret"], None);
    run(&repo, "git", &["mv", "dir", "vault"], None);
    run(&repo, "git", &["mv", "notes.txt", "vault/notes.txt"], None);
    // Status says what the hook will do. Until then Git refuses to decrypt
    // the moved record at its new path, and says how to fix it.
    let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    assert!(status.contains("renamed or invalid") && status.contains("staged unencrypted"), "{status}");
    // Linux and macOS Git hand the diff driver the moved record, which does
    // not open at its new path; Git for Windows hands it the worktree file.
    let out = exec(&repo, "git", &["diff", "--cached", "-M"], None);
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(if cfg!(windows) { out.status.success() || err.contains("run `git add --renormalize -- renamed.secret`") }
        else { !out.status.success() && err.contains("run `git add --renormalize -- renamed.secret`") }, "{err}");
    let err = run_err(&repo, "git", &["commit", "-qm", "moves"], None);
    assert!(err.contains("re-encrypting renamed.secret for its new name (it was a.secret)"), "{err}");
    assert!(err.contains("encrypting vault/notes.txt"), "{err}");
    for path in ["renamed.secret", "vault/b.secret", "vault/c.secret", "vault/notes.txt"] {
        assert!(is_record(&committed(&repo, path)), "{path}");
    }
    run(&repo, bin(), &["verify-index"], None);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    let out = String::from_utf8(run(&repo, bin(), &["audit"], None)).unwrap();
    assert!(out.contains("all authenticated"), "{out}");
    // `git add --renormalize` after the move re-encrypts right away, so
    // `git diff --cached` works before committing too. (A plain `git add`
    // re-cleans only if Git notices the file changed, which a move within
    // the same second as the last write may not show.)
    run(&repo, "git", &["mv", "renamed.secret", "again.secret"], None);
    run(&repo, "git", &["add", "--renormalize", "--", "again.secret"], None);
    let diff = String::from_utf8(run(&repo, "git", &["diff", "--cached", "-M"], None)).unwrap();
    assert!(diff.contains("again.secret") && !diff.contains("TV3F"), "{diff}");
    run(&repo, bin(), &["verify-index"], None);
    run(&repo, "git", &["commit", "-qm", "again"], None);
    let clone = scratch.clone("repo", "clone");
    unlock(&clone);
    assert_eq!(fs::read(clone.join("again.secret")).unwrap(), b"alpha\n");
    assert_eq!(fs::read(clone.join("vault/c.secret")).unwrap(), b"gamma\n");
    assert_eq!(fs::read(clone.join("vault/notes.txt")).unwrap(), b"was public\n");
}

/// While locked nothing can be re-encrypted: a renamed record is refused at
/// commit (its envelope alone would pass), and a record moved without
/// re-encryption (`--no-verify`) is refused by the keyless audit.
#[test]
fn locked_renames_and_unbound_moves_are_refused() {
    let mut scratch = Scratch::new("lockedmv");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
    fs::write(repo.join("a.secret"), b"alpha\n").unwrap();
    commit_all(&repo, "a");
    run(&repo, bin(), &["lock"], None);
    run(&repo, "git", &["mv", "a.secret", "b.secret"], None);
    let err = run_fails(&repo, "git", &["commit", "-qm", "locked move"], None);
    assert!(err.contains("b.secret holds the encrypted a.secret") && err.contains("unlocked"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "unbound move"], None);
    let err = run_fails(&repo, bin(), &["audit"], None);
    assert!(err.contains("moved here without re-encryption"), "{err}");
    // Unlocked again: undo, and the same move goes through.
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    unlock(&repo);
    run(&repo, "git", &["mv", "a.secret", "b.secret"], None);
    run(&repo, "git", &["commit", "-qm", "unlocked move"], None);
    run(&repo, bin(), &["audit"], None);
}

/// `protect` encrypts files that were already tracked (warning that history
/// keeps them), refuses patterns that select repository metadata, and
/// `unprotect` deliberately returns files to plaintext.
#[test]
fn protect_and_unprotect_change_the_policy_explicitly() {
    let mut scratch = Scratch::new("protect");
    let repo = scratch.git_repo("repo");
    fs::write(repo.join("creds.json"), b"{\"token\": \"t\"}\n").unwrap();
    commit(&repo, &["creds.json"], "plaintext creds");
    run(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
    let err = run_err(&repo, bin(), &["protect", "creds.json"], None);
    assert!(err.contains("encrypting creds.json") && err.contains("earlier commits"), "{err}");
    assert!(is_record(&staged(&repo, "creds.json")));
    assert_eq!(fs::read(repo.join("creds.json")).unwrap(), b"{\"token\": \"t\"}\n");
    run(&repo, "git", &["commit", "-qm", "protect creds"], None);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    run(&repo, bin(), &["audit"], None);
    // Protecting again changes nothing.
    run(&repo, bin(), &["protect", "creds.json"], None);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    // Metadata is never encrypted.
    let attributes = fs::read(repo.join(".gitattributes")).unwrap();
    let err = run_fails(&repo, bin(), &["protect", "*"], None);
    assert!(err.contains(".gitattributes") && err.contains("narrower"), "{err}");
    assert_eq!(fs::read(repo.join(".gitattributes")).unwrap(), attributes, "refused edit is undone");
    // A hand-written rule that selects metadata is refused by Git's filter
    // run and by verify-index, with the same explanation.
    fs::write(repo.join(".gitattributes"), [attributes.as_slice(), b".gitattributes transcrypt\n"].concat()).unwrap();
    let err = run_fails(&repo, "git", &["add", ".gitattributes"], None);
    assert!(err.contains("never encrypts .gitattributes"), "{err}");
    fs::write(repo.join(".gitattributes"), &attributes).unwrap();
    // Unprotect: the next commit stores the plaintext, as asked.
    let err = run_err(&repo, bin(), &["unprotect", "creds.json"], None);
    assert!(err.contains("UNENCRYPTED") && err.contains("creds.json"), "{err}");
    assert_eq!(staged(&repo, "creds.json"), b"{\"token\": \"t\"}\n");
    run(&repo, "git", &["commit", "-qm", "unprotect"], None);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    let err = run_fails(&repo, bin(), &["unprotect", "creds.json"], None);
    assert!(err.contains("no `creds.json transcrypt` line"), "{err}");
}

/// A pulled rekey leaves the stored key stale: nothing is decrypted or
/// encrypted with it (files stay ciphertext, plaintext is refused with an
/// explanation) until `unlock` with the new passphrase.
#[test]
fn pulled_rekey_makes_the_stored_key_stale_until_unlock() {
    let mut scratch = Scratch::new("stale");
    let origin = scratch.git_repo("origin");
    run(&origin, bin(), &["init", "--password-stdin", ".env"], Some(PASS));
    fs::write(origin.join(".env"), b"before\n").unwrap();
    commit_all(&origin, "env");
    let clone = scratch.clone("origin", "clone");
    unlock(&clone);
    run(&origin, bin(), &["rekey", "--password-stdin"], Some(NEW));
    run(&origin, "git", &["commit", "-qm", "rekey"], None);
    run(&clone, "git", &["pull", "-q", "--no-rebase"], None);
    assert!(is_record(&fs::read(clone.join(".env")).unwrap()), "a stale key decrypts nothing");
    let status = String::from_utf8(run(&clone, bin(), &["status"], None)).unwrap();
    assert!(status.contains("does not match .transcrypt/config"), "{status}");
    fs::write(clone.join(".env"), b"edited\n").unwrap();
    let err = run_fails(&clone, "git", &["add", ".env"], None);
    assert!(err.contains("rekeyed"), "{err}");
    run(&clone, "git", &["checkout", "--", ".env"], None);
    run(&clone, bin(), &["unlock", "--password-stdin"], Some(NEW));
    assert_eq!(fs::read(clone.join(".env")).unwrap(), b"before\n");
}

/// Review F-02: `rekey` wrote `.transcrypt/config.rekey` with a path-based
/// write that followed a committed symlink out of the repository. The new
/// config is now written through held directory descriptors, never through
/// a symlink, and nothing outside the repository changes.
#[test]
fn rekey_never_writes_through_committed_symlinks() {
    let mut scratch = Scratch::new("rekeylink");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
    fs::write(repo.join("a.secret"), b"alpha\n").unwrap();
    commit_all(&repo, "a");
    let sentinel = scratch.root.join("outside.txt");
    fs::write(&sentinel, b"SENTINEL\n").unwrap();
    symlink(&sentinel, &repo.join(".transcrypt/config.rekey"));
    symlink(&sentinel, &repo.join(".transcrypt/config.tmp"));
    commit(&repo, &[".transcrypt"], "hostile symlinks");
    run(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    assert_eq!(fs::read(&sentinel).unwrap(), b"SENTINEL\n", "rekey wrote outside the repository");
    let meta = fs::symlink_metadata(repo.join(".transcrypt/config")).unwrap();
    assert!(meta.file_type().is_file(), ".transcrypt/config must stay a regular file");
    run(&repo, "git", &["commit", "-qm", "rekey"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha\n");
    run(&repo, bin(), &["lock"], None);
    run(&repo, bin(), &["unlock", "--password-stdin"], Some(NEW));
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha\n");
    // A config that is itself a symlink is refused before anything is written.
    fs::remove_file(repo.join(".transcrypt/config")).unwrap();
    symlink(&sentinel, &repo.join(".transcrypt/config"));
    let err = run_fails(&repo, bin(), &["rekey", "--password-stdin"], Some(PASS));
    assert!(err.contains("unsafe .transcrypt/config"), "{err}");
    assert_eq!(fs::read(&sentinel).unwrap(), b"SENTINEL\n");
    fs::remove_file(repo.join(".transcrypt/config")).unwrap();
    run(&repo, "git", &["checkout", "--", ".transcrypt/config"], None);
}

/// A repository protected by Bash transcrypt (v2) converts to v3 with one
/// explicit command that keeps the selected patterns, re-encrypts the
/// decrypted worktree with v3 and leaves the v2 credentials for the user to
/// remove after checking a fresh clone.
#[test]
#[cfg_attr(target_os = "openbsd", ignore = "Bash transcrypt (v2) needs `head -c`, which OpenBSD lacks")]
fn bash_v2_repositories_migrate_to_v3() {
    let mut scratch = Scratch::new("migrate");
    let repo = scratch.git_repo("repo");
    init_bash_v2(&repo);
    fs::create_dir_all(repo.join("private")).unwrap();
    fs::write(repo.join(".gitattributes"),
        b"*.key filter=crypt diff=crypt merge=crypt\nprivate/** filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join("server.key"), b"v2 protected key\n").unwrap();
    fs::write(repo.join("private/notes"), b"v2 protected notes\n").unwrap();
    commit_all(&repo, "v2 secrets");
    assert!(committed(&repo, "server.key").starts_with(b"U2FsdGVk"), "v2 encrypts");
    // Uncommitted work is refused, nothing changes.
    fs::write(repo.join("server.key"), b"edited\n").unwrap();
    let err = run_fails(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(err.contains("commit or discard"), "{err}");
    assert!(!repo.join(".transcrypt").exists());
    run(&repo, "git", &["checkout", "--", "server.key"], None);
    let err = run_err(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(err.contains("Converted 2 file(s)") && err.contains("--remove-section transcrypt"), "{err}");
    let attributes = String::from_utf8(fs::read(repo.join(".gitattributes")).unwrap()).unwrap();
    assert!(attributes.contains("*.key transcrypt") && attributes.contains("private/** transcrypt")
        && !attributes.contains("filter=crypt"), "{attributes}");
    for path in ["server.key", "private/notes"] {
        assert!(is_record(&staged(&repo, path)), "{path} not v3 ciphertext");
    }
    assert_eq!(fs::read(repo.join("server.key")).unwrap(), b"v2 protected key\n");
    run(&repo, "git", &["commit", "-qm", "convert to v3"], None);
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    run(&repo, bin(), &["audit"], None);
    // A fresh clone needs only v3.
    let clone = scratch.clone("repo", "clone");
    unlock(&clone);
    assert_eq!(fs::read(clone.join("private/notes")).unwrap(), b"v2 protected notes\n");
    // The v2 history is still v2 ciphertext.
    assert!(run(&repo, "git", &["show", "HEAD~1:server.key"], None).starts_with(b"U2FsdGVk"));
}

/// A merge that needs no conflict resolution never runs `pre-commit`; the
/// `pre-merge-commit` hook verifies the merged index instead (read-only),
/// so a branch carrying a moved record is refused before the merge commit
/// exists, and a good branch merges normally.
#[test]
fn merges_are_verified_before_the_merge_commit() {
    let mut scratch = Scratch::new("premerge");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
    fs::write(repo.join("a.secret"), b"alpha\n").unwrap();
    fs::write(repo.join("b.secret"), b"beta\n").unwrap();
    commit_all(&repo, "secrets");
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    // A branch that moves a.secret's record over b.secret without re-encryption.
    run(&repo, "git", &["checkout", "-q", "-b", "hostile"], None);
    let a_oid = String::from_utf8(run(&repo, "git", &["rev-parse", ":a.secret"], None)).unwrap();
    run(&repo, "git", &["update-index", "--cacheinfo", REGULAR_FILE_MODE, a_oid.trim(), "b.secret"], None);
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "hostile move"], None);
    run(&repo, "git", &["checkout", "-q", "-f", main.trim()], None);
    fs::write(repo.join("README"), b"diverge\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "diverge"], None);
    // Unlocked, the merge's own checkout refuses to decrypt the moved record.
    let err = run_fails(&repo, "git", &["merge", "-q", "--no-edit", "hostile"], None);
    assert!(err.contains("does not open at b.secret"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD"], None);
    run(&repo, bin(), &["hydrate"], None);
    // Locked, checkout keeps records encrypted, so the pre-merge-commit hook
    // is what refuses: b.secret holds a.secret's record.
    run(&repo, bin(), &["lock"], None);
    let err = run_fails(&repo, "git", &["merge", "-q", "--no-edit", "hostile"], None);
    assert!(err.contains("b.secret holds the encrypted a.secret"), "{err}");
    let _ = exec(&repo, "git", &["merge", "--abort"], None);
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD"], None);
    unlock(&repo);
    // An honest branch merges without ceremony.
    run(&repo, "git", &["checkout", "-q", "-b", "honest", "HEAD~1"], None);
    fs::write(repo.join("a.secret"), b"alpha v2\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "edit"], None);
    run(&repo, "git", &["checkout", "-q", main.trim()], None);
    run(&repo, "git", &["merge", "-q", "--no-edit", "honest"], None);
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"alpha v2\n");
    run(&repo, bin(), &["audit"], None);
}

/// Git finds renames by content similarity, and a record re-encrypted for
/// its new path shares no bytes with the old one. So a protected file
/// renamed on one branch and edited on the other merges as a modify/delete
/// conflict. That conflict is recoverable in plaintext: both versions are
/// decrypted in the worktree, and the resolution is committed encrypted.
#[test]
fn rename_and_edit_on_two_branches_conflict_in_plaintext() {
    let mut scratch = Scratch::new("renamemerge");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
    fs::write(repo.join("a.secret"), b"one\ntwo\n").unwrap();
    commit_all(&repo, "base");
    run(&repo, "git", &["checkout", "-q", "-b", "renamed"], None);
    run(&repo, "git", &["mv", "a.secret", "b.secret"], None);
    run(&repo, "git", &["commit", "-qm", "rename"], None);
    run(&repo, "git", &["checkout", "-q", "-b", "edited", "HEAD~1"], None);
    fs::write(repo.join("a.secret"), b"one\nTWO\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "edit"], None);
    let err = String::from_utf8_lossy(&exec(&repo, "git", &["merge", "--no-edit", "renamed"], None).stdout).into_owned();
    assert!(err.contains("CONFLICT (modify/delete): a.secret"), "{err}");
    assert_eq!(fs::read(repo.join("a.secret")).unwrap(), b"one\nTWO\n", "our edit, decrypted");
    assert_eq!(fs::read(repo.join("b.secret")).unwrap(), b"one\ntwo\n", "their rename, decrypted");
    fs::write(repo.join("b.secret"), b"one\nTWO\n").unwrap();
    run(&repo, "git", &["rm", "-q", "a.secret"], None);
    commit(&repo, &["b.secret"], "merge: keep the edit under the new name");
    assert!(is_record(&committed(&repo, "b.secret")));
    run(&repo, bin(), &["audit"], None);
}

/// Ordinary Git commands need no Transcrypt step in the default mode:
/// cherry-pick, revert, restore from another commit, reset, switch, an
/// interactive rebase and stash all leave decrypted files and a clean,
/// verified, auditable repository.
#[test]
fn everyday_git_commands_just_work() {
    let mut scratch = Scratch::new("everyday");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.secret"], Some(PASS));
    fs::write(repo.join("x.secret"), b"v1\n").unwrap();
    commit_all(&repo, "v1");
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    let main = main.trim();
    run(&repo, "git", &["switch", "-q", "-c", "side"], None);
    fs::write(repo.join("x.secret"), b"v2\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "v2"], None);
    let side = String::from_utf8(run(&repo, "git", &["rev-parse", "HEAD"], None)).unwrap();
    let side = side.trim();
    run(&repo, "git", &["switch", "-q", main], None);
    let read = || fs::read(repo.join("x.secret")).unwrap();
    for (args, expected) in [
        (vec!["cherry-pick", side], &b"v2\n"[..]),
        (vec!["revert", "--no-edit", "HEAD"], b"v1\n"),
        (vec!["restore", "--source", side, "x.secret"], b"v2\n"),
        (vec!["reset", "-q", "--hard"], b"v1\n"),
        (vec!["switch", "-q", "side"], b"v2\n"),
        (vec!["switch", "-q", main], b"v1\n"),
        (vec!["stash", "-q"], b"v1\n"),
    ] {
        if args[0] == "stash" { fs::write(repo.join("x.secret"), b"work in progress\n").unwrap(); }
        run(&repo, "git", &args, None);
        assert_eq!(read(), expected, "after git {args:?}");
    }
    run(&repo, "git", &["stash", "pop", "-q"], None);
    assert_eq!(read(), b"work in progress\n");
    run(&repo, "git", &["checkout", "-q", "--", "x.secret"], None);
    run(&repo, "sh", &["-c", "GIT_SEQUENCE_EDITOR=true exec git rebase -q -i HEAD~2"], None);
    assert_eq!(read(), b"v1\n");
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    run(&repo, bin(), &["verify-index"], None);
    let out = String::from_utf8(run(&repo, bin(), &["audit", "--all"], None)).unwrap();
    assert!(out.contains("all authenticated"), "{out}");
}

/// Review F1: `protect` refuses patterns that would select nothing (a
/// directory, a negation, a name Git reads as a glob), accepts `./x`, and
/// leaves `.gitattributes` unchanged when it refuses.
#[test]
fn protect_refuses_patterns_that_select_nothing() {
    let mut scratch = Scratch::new("patterncheck");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
    run(&repo, "git", &["commit", "-qm", "init"], None);
    fs::create_dir(repo.join("secrets")).unwrap();
    fs::write(repo.join("secrets/key.txt"), b"TOPSECRET\n").unwrap();
    // A backslash is a separator on Windows, not a name character.
    if cfg!(unix) { fs::write(repo.join("back\\slash.txt"), b"SLASHED\n").unwrap(); }
    fs::write(repo.join("x.env"), b"X\n").unwrap();
    let before = fs::read(repo.join(".gitattributes")).unwrap();
    let patterns = [("secrets/", "secrets/**"), ("secrets", "secrets/**"), ("!x.env", "no negative"),
                    ("back\\slash.txt", "glob characters")];
    // The last pattern names a file that only Unix can have.
    let tested = if cfg!(unix) { &patterns[..] } else { &patterns[..patterns.len() - 1] };
    for (pattern, says) in tested {
        let err = run_fails(&repo, bin(), &["protect", pattern], None);
        assert!(err.contains(says), "{pattern}: {err}");
        assert_eq!(fs::read(repo.join(".gitattributes")).unwrap(), before, "{pattern} left an edit");
        assert!(run(&repo, "git", &["diff", "--cached", "--name-only"], None).is_empty(), "{pattern} staged");
    }
    run(&repo, bin(), &["protect", "./x.env", "secrets/**"], None);
    commit_all(&repo, "protected");
    assert!(is_record(&committed(&repo, "x.env")) && is_record(&committed(&repo, "secrets/key.txt")));
}

/// Review F2: moving a protected file to an unprotected name would commit a
/// record that nothing decrypts there; the hook and the audit refuse it.
#[test]
fn records_moved_to_unprotected_names_are_refused() {
    let mut scratch = Scratch::new("unprotectedmove");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("prod.env"), b"PROD_SECRET\n").unwrap();
    commit_all(&repo, "secret");
    run(&repo, "git", &["mv", "prod.env", "prod.env.bak"], None);
    let err = run_fails(&repo, "git", &["commit", "-qm", "backup"], None);
    assert!(err.contains("prod.env.bak holds an encrypted record but is not protected"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "backup"], None);
    let err = run_fails(&repo, bin(), &["audit"], None);
    assert!(err.contains("moved to this unprotected name"), "{err}");
}

/// Review F3: `unprotect` decrypts a staged rename at its source path, and
/// commits the plaintext; review F6: protecting by hand-editing
/// `.gitattributes` is completed by `protect`, as the hook's error says.
#[test]
fn unprotect_follows_renames_and_protect_finishes_manual_rules() {
    let mut scratch = Scratch::new("unprotectmv");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"PROD\n").unwrap();
    fs::write(repo.join("config.ini"), b"pw=1\n").unwrap();
    commit_all(&repo, "files");
    run(&repo, "git", &["mv", "a.env", "b.env"], None);
    run(&repo, bin(), &["unprotect", "*.env"], None);
    assert_eq!(staged(&repo, "b.env"), b"PROD\n");
    run(&repo, "git", &["commit", "-qm", "unprotect"], None);
    run(&repo, bin(), &["audit"], None);
    // A rule added by hand to a file tracked in plaintext.
    let mut attributes = fs::read(repo.join(".gitattributes")).unwrap();
    attributes.extend_from_slice(b"config.ini transcrypt\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    run(&repo, "git", &["add", ".gitattributes"], None);
    let err = run_fails(&repo, "git", &["commit", "-qm", "manual rule"], None);
    assert!(err.contains("config.ini is not encrypted") && err.contains("transcrypt-rs protect"), "{err}");
    run(&repo, bin(), &["protect", "config.ini"], None);
    run(&repo, "git", &["commit", "-qm", "manual rule"], None);
    assert!(is_record(&committed(&repo, "config.ini")));
}

/// Review F5: renaming while a secret is rotated (a new file at the old
/// name), and renaming during a stopped interactive rebase, are local
/// changes and are re-encrypted.
#[test]
fn renames_during_rotation_and_rebase_stops_work() {
    let mut scratch = Scratch::new("rotation");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("prod.env"), b"OLD\n").unwrap();
    commit_all(&repo, "v1");
    run(&repo, "git", &["mv", "prod.env", "old.env"], None);
    fs::write(repo.join("prod.env"), b"NEW\n").unwrap();
    commit(&repo, &["prod.env"], "rotate");
    run(&repo, bin(), &["audit"], None);
    // Stop at a commit during an interactive rebase and rename there.
    run(&repo, "sh", &["-c", "GIT_SEQUENCE_EDITOR='sed -i.orig s/^pick/edit/' exec git rebase -q -i HEAD~1"], None);
    run(&repo, "git", &["mv", "old.env", "older.env"], None);
    run(&repo, "git", &["commit", "-q", "--amend", "--no-edit"], None);
    run(&repo, "git", &["rebase", "--continue"], None);
    run(&repo, bin(), &["verify-index"], None);
    run(&repo, bin(), &["audit"], None);
    let clone = scratch.clone("repo", "clone");
    unlock(&clone);
    assert_eq!(fs::read(clone.join("older.env")).unwrap(), b"OLD\n");
    assert_eq!(fs::read(clone.join("prod.env")).unwrap(), b"NEW\n");
}

/// Review F4: quoted v2 patterns are converted, and v2 rules in
/// `.git/info/attributes` are refused instead of silently dropped.
#[test]
#[cfg_attr(target_os = "openbsd", ignore = "Bash transcrypt (v2) needs `head -c`, which OpenBSD lacks")]
fn migrate_converts_quoted_rules_and_refuses_local_ones() {
    let mut scratch = Scratch::new("migratequoted");
    let repo = scratch.git_repo("repo");
    init_bash_v2(&repo);
    fs::write(repo.join(".gitattributes"), b"\"my secret.txt\" filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join("my secret.txt"), b"quoted v2 secret\n").unwrap();
    fs::write(repo.join("local.key"), b"local rule secret\n").unwrap();
    fs::write(repo.join(".git/info/attributes"), b"local.key filter=crypt diff=crypt merge=crypt\n").unwrap();
    commit_all(&repo, "v2");
    let err = run_fails(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(err.contains("info/attributes") && err.contains("move them"), "{err}");
    // As the message says: move the rule into .gitattributes and commit it.
    fs::write(repo.join(".gitattributes"),
        b"\"my secret.txt\" filter=crypt diff=crypt merge=crypt\nlocal.key filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join(".git/info/attributes"), b"").unwrap();
    run(&repo, "git", &["commit", "-qam", "rule moved"], None);
    run(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(is_record(&staged(&repo, "local.key")));
    assert!(String::from_utf8(fs::read(repo.join(".gitattributes")).unwrap()).unwrap()
        .contains("\"my secret.txt\" transcrypt"));
    assert!(is_record(&staged(&repo, "my secret.txt")));
}

/// Second review F1/F2: a commit cherry-picked or rebased across a rekey
/// keeps records of the earlier config. Git keeps working (status, the
/// commit is never dropped), v3 says what happened, and `reencrypt` with the
/// earlier passphrase fixes it. Switching branches across the rekey decrypts
/// with the key that matches each file, whatever order Git writes them in.
#[test]
fn work_across_a_rekey_is_kept_and_reencrypted() {
    let mut scratch = Scratch::new("acrossrekey");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env", "*.key"], Some(PASS));
    fs::write(repo.join(".env"), b"dot env\n").unwrap();
    fs::write(repo.join("z.key"), b"zed\n").unwrap();
    commit_all(&repo, "init");
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    let main = main.trim().to_owned();
    run(&repo, "git", &["checkout", "-q", "-b", "feature"], None);
    fs::write(repo.join("b.env"), b"feature secret\n").unwrap();
    commit(&repo, &["b.env"], "addb");
    run(&repo, "git", &["checkout", "-q", &main], None);
    run(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    run(&repo, "git", &["commit", "-qm", "rekey"], None);
    // Back and forth across the rekey: each side decrypts with its key.
    run(&repo, "git", &["checkout", "-q", "HEAD~1"], None);
    run(&repo, "git", &["checkout", "-q", &main], None);
    assert_eq!(fs::read(repo.join(".env")).unwrap(), b"dot env\n");
    assert_eq!(fs::read(repo.join("z.key")).unwrap(), b"zed\n");
    // Cherry-pick across the rekey: Git keeps working, v3 explains.
    let err = String::from_utf8_lossy(&exec(&repo, "git", &["cherry-pick", "feature"], None).stderr).into_owned();
    assert!(err.contains("b.env is encrypted under another config"), "{err}");
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());
    let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    assert!(status.contains("other config (reencrypt)"), "{status}");
    let err = run_fails(&repo, bin(), &["verify-index"], None);
    assert!(err.contains("transcrypt-rs reencrypt"), "{err}");
    // An explicit decision: it lists what will be trusted and needs --yes.
    let err = run_fails(&repo, bin(), &["reencrypt", "--password-stdin"], Some(PASS));
    assert!(err.contains("b.env (config") && err.contains("addb") && err.contains("not confirmed"), "{err}");
    run(&repo, bin(), &["reencrypt", "--yes", "--password-stdin"], Some(PASS));
    assert_eq!(fs::read(repo.join("b.env")).unwrap(), b"feature secret\n");
    run(&repo, "git", &["commit", "-q", "--amend", "--no-edit"], None);
    run(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
    // Rebasing the branch onto the rekey keeps its commit.
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&repo, "git", &["checkout", "-q", "feature"], None);
    run(&repo, "git", &["rebase", "-q", &main], None);
    let log = String::from_utf8(run(&repo, "git", &["log", "--format=%s"], None)).unwrap();
    assert!(log.starts_with("addb\nrekey\n"), "{log}");
    run(&repo, bin(), &["reencrypt", "--yes", "--password-stdin"], Some(PASS));
    run(&repo, "git", &["commit", "-q", "--amend", "--no-edit"], None);
    run(&repo, bin(), &["verify-index"], None);
}

/// Second review F3/F4/F5: an existing `transcrypt` macro definition is
/// refused instead of silently disabling protection; `lock` keeps the key
/// while another worktree holds plaintext; `rekey` refuses a deleted file
/// before changing anything.
#[test]
fn macro_conflicts_other_worktrees_and_deleted_files_are_refused() {
    let mut scratch = Scratch::new("review2");
    let repo = scratch.git_repo("macro");
    fs::write(repo.join(".gitattributes"), b"[attr]transcrypt -diff\n*.txt text\n").unwrap();
    commit(&repo, &[".gitattributes"], "attributes");
    let err = run_fails(&repo, bin(), &["init", "--password-stdin", "secrets/**"], Some(PASS));
    assert!(err.contains("already defines the `transcrypt` macro"), "{err}");
    assert!(!repo.join(".transcrypt").exists());
    assert_eq!(fs::read(repo.join(".gitattributes")).unwrap(), b"[attr]transcrypt -diff\n*.txt text\n");

    let repo = scratch.git_repo("worktrees");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"s1\n").unwrap();
    commit_all(&repo, "init");
    run(&repo, "git", &["branch", "old"], None);
    run(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    run(&repo, "git", &["commit", "-qm", "rekey"], None);
    let linked = scratch.root.join("linked");
    run(&repo, "git", &["worktree", "add", "-q", linked.to_str().unwrap(), "old"], None);
    unlock(&linked);
    assert_eq!(fs::read(linked.join("a.env")).unwrap(), b"s1\n");
    fs::remove_file(repo.join("a.env")).unwrap();
    run(&repo, "git", &["checkout", "--", "a.env"], None);
    let err = run_fails(&repo, bin(), &["lock"], None);
    assert!(err.contains("still holds plaintext"), "{err}");
    assert!(repo.join(".git/transcrypt-v3/key").exists(), "the key must be kept");
    let err = run_fails(&repo, bin(), &["uninstall"], None);
    assert!(err.contains("still holds plaintext"), "{err}");
    run(&linked, bin(), &["lock"], None);
    scratch.repos.push(linked);

    let repo = scratch.git_repo("deleted");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"a\n").unwrap();
    fs::write(repo.join("b.env"), b"b\n").unwrap();
    commit_all(&repo, "init");
    let config = fs::read(repo.join(".transcrypt/config")).unwrap();
    fs::remove_file(repo.join("b.env")).unwrap();
    let err = run_fails(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    assert!(err.contains("b.env has uncommitted changes (or was deleted)"), "{err}");
    assert_eq!(fs::read(repo.join(".transcrypt/config")).unwrap(), config, "nothing changed");
}

/// Private mode's optional session expiration: the agent forgets the key
/// after the idle limit (and the checkout is then locked), but any use
/// before that keeps it alive.
#[test]
fn private_sessions_expire_when_idle() {
    let mut scratch = Scratch::new("expire");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    let err = run_fails(&repo, bin(), &["unlock", "--timeout=2s", "--password-stdin"], Some(PASS));
    assert!(err.contains("--private"), "{err}");
    let err = run_fails(&repo, bin(), &["unlock", "--private", "--timeout=0", "--password-stdin"], Some(PASS));
    assert!(err.contains("positive duration"), "{err}");
    // Robust against slow machines: the uses together span more than the
    // limit, so a session still alive after them was kept alive by them,
    // while each gap leaves ample slack for a slow `status`.
    const LIMIT: Duration = Duration::from_secs(20);
    const PAUSE: Duration = Duration::from_secs(8);
    const USES: u32 = 3;
    const EXPIRY_MARGIN: Duration = Duration::from_secs(10);
    const _: () = assert!(PAUSE.as_secs() * USES as u64 > LIMIT.as_secs());
    let status = || String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    run(&repo, bin(), &["unlock", "--private", &format!("--timeout={}s", LIMIT.as_secs()), "--password-stdin"], Some(PASS));
    let unlocked = Instant::now();
    for _ in 0..USES {
        std::thread::sleep(PAUSE);
        assert!(status().contains("unlocked (private"), "use keeps the session alive");
    }
    assert!(unlocked.elapsed() > LIMIT);
    std::thread::sleep(LIMIT + EXPIRY_MARGIN);
    assert!(status().contains("key:        locked"), "{}", status());
    assert!(!repo.join(".git/transcrypt-v3/session.sock").exists());
}

/// Third review F1: clean lets another config's record through only when
/// Git already has exactly those bytes for the path; plaintext appended
/// after such a header, or a record from elsewhere, is refused.
#[test]
fn foreign_records_pass_clean_only_as_gits_own_blobs() {
    let mut scratch = Scratch::new("foreignclean");
    let other = scratch.git_repo("other");
    run(&other, bin(), &["init", "--password-stdin", "*.env"], Some(NEW));
    let foreign = run(&other, bin(), &["clean", "a.env"], Some(b"other repository\n"));
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    for bytes in [foreign.clone(), [foreign.as_slice(), b"TOPSECRET=leaked\n"].concat()] {
        fs::write(repo.join("a.env"), &bytes).unwrap();
        let err = run_fails(&repo, "git", &["add", "a.env"], None);
        assert!(err.contains("not the one Git has for it"), "{err}");
    }
}

/// Third review F2/F3: a linked worktree on a branch from before a rekey
/// that cherry-picks newer work keeps a working `git status`; `reencrypt`
/// refuses to move content under a config the branch never had before.
#[test]
fn old_branches_stay_usable_and_reencrypt_only_goes_forward() {
    let mut scratch = Scratch::new("oldbranch");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"a\n").unwrap();
    commit_all(&repo, "init");
    run(&repo, "git", &["branch", "old"], None);
    run(&repo, bin(), &["rekey", "--password-stdin"], Some(NEW));
    run(&repo, "git", &["commit", "-qm", "rekey"], None);
    fs::write(repo.join("b.env"), b"created after the rekey\n").unwrap();
    commit(&repo, &["b.env"], "addb");
    let linked = scratch.root.join("linked");
    run(&repo, "git", &["worktree", "add", "-q", linked.to_str().unwrap(), "old"], None);
    scratch.repos.push(linked.clone());
    let main = String::from_utf8(run(&repo, "git", &["branch", "--show-current"], None)).unwrap();
    run(&linked, "git", &["cherry-pick", main.trim()], None);
    assert_eq!(fs::read(linked.join("b.env")).unwrap(), b"created after the rekey\n");
    assert!(run(&linked, "git", &["status", "--porcelain"], None).is_empty());
    // Unlocking with the old passphrase, then trying to pull the newer
    // record back under the old config, is refused.
    unlock(&linked);
    let err = run_fails(&linked, bin(), &["reencrypt", "--yes", "--password-stdin"], Some(NEW));
    assert!(err.contains("never had before"), "{err}");
}

/// Third review F4/F5/F6: a key file from an earlier version counts as
/// locked (unlock replaces it); a quoted redefinition of the macro in a
/// local attribute file stops the commit; a CRLF `.gitattributes` still
/// works with `protect`.
#[test]
fn legacy_keys_macro_redefinitions_and_crlf() {
    let mut scratch = Scratch::new("review3");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"S=1\n").unwrap();
    commit_all(&repo, "init");
    fs::write(repo.join(".git/transcrypt-v3/key"), [7u8; KEY_SIZE]).unwrap();
    let status = String::from_utf8(run(&repo, bin(), &["status"], None)).unwrap();
    assert!(status.contains("key:        locked"), "{status}");
    unlock(&repo);
    assert_eq!(fs::metadata(repo.join(".git/transcrypt-v3/key")).unwrap().len(), KEY_FILE_LEN as u64);
    // Any other length is damaged (the verified `stored_key_state`), and
    // `unlock` repairs it.
    let stored = fs::read(repo.join(".git/transcrypt-v3/key")).unwrap();
    for damaged in [&stored[..KEY_FILE_LEN - 1], &[&stored[..], b"x"].concat()[..]] {
        fs::write(repo.join(".git/transcrypt-v3/key"), damaged).unwrap();
        let err = run_fails(&repo, bin(), &["verify-index"], None);
        assert!(err.contains("damaged .git/transcrypt-v3/key"), "{err}");
    }
    unlock(&repo);
    assert_eq!(fs::read(repo.join(".git/transcrypt-v3/key")).unwrap(), stored);
    // A quoted macro redefinition in .git/info/attributes.
    fs::write(repo.join(".git/info/attributes"), b"\"[attr]transcrypt\" -diff\n").unwrap();
    fs::write(repo.join("a.env"), b"S=3\n").unwrap();
    let err = run_fails(&repo, "git", &["commit", "-qam", "x"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    assert!(!run(&repo, "git", &["show", "HEAD:a.env"], None).starts_with(b"S=3"));
    assert!(!exec(&repo, bin(), &["doctor"], None).status.success());
    fs::remove_file(repo.join(".git/info/attributes")).unwrap();
    run(&repo, "git", &["checkout", "--", "a.env"], None);
    // CRLF line endings in .gitattributes.
    let text = fs::read(repo.join(".gitattributes")).unwrap();
    let crlf: Vec<u8> = text.split(|b| *b == b'\n').map(|l| l.to_vec()).collect::<Vec<_>>().join(&b"\r\n"[..]);
    fs::write(repo.join(".gitattributes"), crlf).unwrap();
    // Commit the CRLF itself (Git for Windows would otherwise normalize it).
    run(&repo, "git", &["config", "core.autocrlf", "false"], None);
    run(&repo, "git", &["commit", "-qam", "crlf"], None);
    fs::write(repo.join("k.key"), b"K\n").unwrap();
    run(&repo, bin(), &["protect", "*.key"], None);
    commit(&repo, &["k.key"], "key");
    assert!(is_record(&committed(&repo, "k.key")));
}

/// Fourth review F-1: a file encrypted in `HEAD` that a later rule hands to
/// another filter (what `git lfs track` writes) is refused by the hook and
/// by the audit, instead of being committed in plaintext silently.
#[test]
fn protection_lost_to_another_filter_is_refused() {
    let mut scratch = Scratch::new("drift");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"A=1\n").unwrap();
    commit_all(&repo, "init");
    let mut attributes = fs::read(repo.join(".gitattributes")).unwrap();
    attributes.extend_from_slice(b"*.env filter=lfs diff=lfs merge=lfs -text\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    fs::write(repo.join("a.env"), b"A=rotated-secret\n").unwrap();
    run(&repo, "git", &["add", ".gitattributes", "a.env"], None);
    let err = run_fails(&repo, "git", &["commit", "-qm", "track env in lfs"], None);
    assert!(err.contains("a.env") && err.contains("`lfs`"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "track env in lfs"], None);
    let err = run_fails(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
    assert!(err.contains("a.env") && err.contains("`lfs`"), "{err}");
    // Deliberately unprotecting is still allowed.
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    run(&repo, bin(), &["unprotect", "*.env"], None);
    run(&repo, "git", &["commit", "-qm", "unprotect"], None);
    run(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
}

/// Fourth review F-2/F-3/F-4/F-6: patterns inside submodules are refused;
/// hooks written by a binary that has since moved are recognized and
/// rewritten by `unlock`; a sparse checkout without `.transcrypt/` keeps
/// working; `reencrypt` is an explicit, confirmed decision.
#[test]
fn submodules_moved_binaries_sparse_checkouts_and_confirmation() {
    let mut scratch = Scratch::new("review4");
    let inner = scratch.git_repo("inner");
    fs::write(inner.join("token.env"), b"TOKEN=1\n").unwrap();
    commit_all(&inner, "token");
    let outer = scratch.git_repo("outer");
    run(&outer, "git", &["-c", "protocol.file.allow=always", "submodule", "add", "-q", "../inner", "libsec"], None);
    run(&outer, "git", &["commit", "-qm", "submodule"], None);
    run(&outer, bin(), &["init", "--password-stdin"], Some(PASS));
    let err = run_fails(&outer, bin(), &["protect", "libsec/token.env"], None);
    assert!(err.contains("inside the submodule libsec"), "{err}");

    // A binary at another path installed the hooks and filters.
    let moved = scratch.root.join("old-install");
    fs::create_dir(&moved).unwrap();
    // Under its name before the rename: its hooks are still ours.
    let old_bin = moved.join(format!("transcrypt-v3{}", std::env::consts::EXE_SUFFIX));
    fs::copy(bin(), &old_bin).unwrap();
    let repo = scratch.git_repo("moved");
    run(&repo, old_bin.to_str().unwrap(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::remove_dir_all(&moved).unwrap();
    run(&repo, bin(), &["unlock"], None);
    fs::write(repo.join("a.env"), b"A\n").unwrap();
    commit_all(&repo, "after moving the binary");
    assert!(is_record(&committed(&repo, "a.env")));
    assert!(exec(&repo, bin(), &["doctor"], None).status.success());

    // Sparse checkout that leaves out .transcrypt/.
    fs::create_dir(repo.join("app")).unwrap();
    fs::write(repo.join("app/s.env"), b"S\n").unwrap();
    commit_all(&repo, "app");
    run(&repo, "git", &["sparse-checkout", "set", "app"], None);
    assert!(!repo.join(".transcrypt").exists());
    fs::write(repo.join("app/s.env"), b"S2\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "sparse edit"], None);
    assert!(is_record(&committed(&repo, "app/s.env")));
    run(&repo, "git", &["sparse-checkout", "disable"], None);

}

/// Fifth review F1/F2/F3: a migration whose passphrase step fails changes
/// nothing; losing the `transcrypt` macro (an overwritten `.gitattributes`)
/// is refused by the hook and the audit; selection is case-sensitive on
/// every clone, so a pattern matching only case-insensitively fails closed.
#[test]
#[cfg_attr(target_os = "openbsd", ignore = "Bash transcrypt (v2) needs `head -c`, which OpenBSD lacks")]
fn interrupted_migration_lost_macro_and_case_sensitivity() {
    let mut scratch = Scratch::new("review5");
    let repo = scratch.git_repo("migrate");
    init_bash_v2(&repo);
    fs::write(repo.join(".gitattributes"), b"*.key filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join("db.key"), b"v2 secret\n").unwrap();
    commit_all(&repo, "v2");
    let hook = fs::read(repo.join(".git/hooks/pre-commit")).unwrap();
    run_fails(&repo, bin(), &["migrate", "--password-stdin"], Some(b"short\n"));
    assert_eq!(fs::read(repo.join(".gitattributes")).unwrap(), b"*.key filter=crypt diff=crypt merge=crypt\n");
    assert_eq!(fs::read(repo.join(".git/hooks/pre-commit")).unwrap(), hook, "Bash hook untouched");
    assert!(run(&repo, "git", &["status", "--porcelain"], None).is_empty());

    let repo = scratch.git_repo("macro");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"S=1\n").unwrap();
    commit_all(&repo, "init");
    fs::write(repo.join(".gitattributes"), b"*.png binary\n").unwrap();
    let err = run_fails(&repo, "git", &["commit", "-qam", "clobber"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-am", "clobber"], None);
    let err = run_fails(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);

    run(&repo, "git", &["config", "core.ignorecase", "true"], None);
    fs::write(repo.join("PROD.ENV"), b"P=1\n").unwrap();
    run(&repo, "git", &["add", "PROD.ENV"], None);
    let err = run_fails(&repo, "git", &["commit", "-qm", "upper"], None);
    assert!(err.contains("PROD.ENV holds an encrypted record but is not protected") && err.contains("case"), "{err}");
}

/// Fifth review F5/F6: a foreign one-line hook that merely ends in
/// `transcrypt-v3` is never taken for ours; a non-executable v3 hook is
/// reported by `doctor` and repaired by `unlock`; a new passphrase must be
/// one line.
#[test]
fn foreign_hooks_executable_bits_and_one_line_passphrases() {
    let mut scratch = Scratch::new("hooks5");
    let repo = scratch.git_repo("repo");
    let err = run_fails(&repo, bin(), &["init", "--password-stdin"], Some(b"long enough passphrase\n\n"));
    assert!(err.contains("one line"), "{err}");
    fs::create_dir_all(repo.join(".git/hooks")).unwrap();
    let foreign = "#!/bin/sh\nexec '/opt/ci/run-lint-and-transcrypt-v3' pre-commit\n";
    fs::write(repo.join(".git/hooks/pre-commit"), foreign).unwrap();
    let err = run_fails(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    assert!(err.contains("not the v3 hook"), "{err}");
    assert_eq!(fs::read_to_string(repo.join(".git/hooks/pre-commit")).unwrap(), foreign);
    fs::remove_file(repo.join(".git/hooks/pre-commit")).unwrap();
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    // Git for Windows runs a hook whatever its permissions.
    #[cfg(unix)]
    {
        for hook in ["pre-commit", "pre-push"] {
            fs::set_permissions(repo.join(".git/hooks").join(hook), fs::Permissions::from_mode(modes::PRIVATE_FILE)).unwrap();
        }
        let out = String::from_utf8(exec(&repo, bin(), &["doctor"], None).stdout).unwrap();
        assert!(out.contains("FAIL pre-commit hook installed"), "{out}");
        run(&repo, bin(), &["unlock"], None);
    }
    assert!(exec(&repo, bin(), &["doctor"], None).status.success());
}

/// Sixth review F1/F2: the hooks and the audit enforce one predicate. A
/// redefinition of the macro later in `.gitattributes` is refused by the
/// read-only check (merge commits) and by the audit; a commit on a branch
/// from before `init` passes the hooks exactly as it passes the audit.
#[test]
fn hooks_and_audit_agree_on_the_macro_and_configless_branches() {
    let mut scratch = Scratch::new("review6");
    let repo = scratch.git_repo("repo");
    run(&repo, "git", &["branch", "before-init"], None);
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"S=1\n").unwrap();
    commit_all(&repo, "init");
    let mut attributes = fs::read(repo.join(".gitattributes")).unwrap();
    attributes.extend_from_slice(b"[attr]transcrypt -text\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    fs::write(repo.join("n.env"), b"NEW=plain\n").unwrap();
    run(&repo, "git", &["add", "-A"], None);
    let err = run_fails(&repo, bin(), &["verify-index"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "redefine"], None);
    let err = run_fails(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    // A branch from before init: ordinary commits pass, as in the audit.
    run(&repo, "git", &["checkout", "-q", "before-init"], None);
    fs::write(repo.join("README"), b"edited on an old branch\n").unwrap();
    run(&repo, "git", &["commit", "-qam", "old branch work"], None);
    run(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
}

/// Sixth review F3/F5: rerunning an interrupted `init`, `unprotect` or
/// `migrate` completes it; `migrate` never finishes with v2 ciphertext left
/// over (here: a file Bash selected only case-insensitively).
#[test]
#[cfg(unix)] // The interruption is a shell script named `git` on PATH.
#[cfg_attr(target_os = "openbsd", ignore = "Bash transcrypt (v2) needs `head -c`, which OpenBSD lacks")]
fn interrupted_commands_converge_when_rerun() {
    let mut scratch = Scratch::new("converge");
    // init: config written but never committed (an interruption).
    let repo = scratch.git_repo("init");
    run(&repo, bin(), &["init", "--password-stdin"], Some(PASS));
    let err = run_fails(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(NEW));
    assert!(err.contains("interrupted init") && err.contains("start over"), "{err}");
    fs::write(repo.join("a.env"), b"A\n").unwrap();
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    commit_all(&repo, "init");
    assert!(is_record(&committed(&repo, "a.env")));
    // unprotect: the worktree rules already lost the line.
    let rules = fs::read_to_string(repo.join(".gitattributes")).unwrap();
    fs::write(repo.join(".gitattributes"), rules.replace("*.env transcrypt\n", "")).unwrap();
    run(&repo, bin(), &["unprotect", "*.env"], None);
    assert_eq!(staged(&repo, "a.env"), b"A\n");

    // migrate: killed during re-encryption, then rerun.
    let repo = scratch.git_repo("migrate");
    init_bash_v2(&repo);
    fs::write(repo.join(".gitattributes"), b"*.key filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join("db.key"), b"v2 secret\n").unwrap();
    commit_all(&repo, "v2");
    assert!(!migrate_with_shim(&scratch.root.join("shim"), &repo, KILL).status.success(), "the shim kills migrate");
    run(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(is_record(&staged(&repo, "db.key")));
    run(&repo, "git", &["commit", "-qm", "converted"], None);
    run(&repo, bin(), &["audit"], None);

    // migrate: a v2 file selected only case-insensitively is not left behind.
    let repo = scratch.git_repo("case");
    run(&repo, "git", &["config", "core.ignorecase", "true"], None);
    init_bash_v2(&repo);
    fs::write(repo.join(".gitattributes"), b"*.env filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join("a.env"), b"a\n").unwrap();
    fs::write(repo.join("PROD.ENV"), b"prod\n").unwrap();
    commit_all(&repo, "v2");
    assert!(committed(&repo, "PROD.ENV").starts_with(b"U2FsdGVk"));
    let err = run_fails(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(err.contains("PROD.ENV is still v2 ciphertext"), "{err}");
    assert!(!repo.join(".transcrypt").exists(), "rolled back");
    assert_eq!(fs::read(repo.join(".gitattributes")).unwrap(), b"*.env filter=crypt diff=crypt merge=crypt\n");
    assert!(run(&repo, "git", &["status", "--porcelain", "--untracked-files=no"], None).is_empty());
}

/// Seventh review F1/F2: a rule aimed at the macro probe's own path does
/// not satisfy the macro check (real paths are checked too); `--amend`
/// is judged against the commit's parent, as the audit does.
#[test]
fn probe_spoofs_and_amends_are_refused() {
    let mut scratch = Scratch::new("review7");
    let repo = scratch.git_repo("repo");
    run(&repo, bin(), &["init", "--password-stdin", "*.env"], Some(PASS));
    fs::write(repo.join("a.env"), b"S=1\n").unwrap();
    fs::write(repo.join("x.env"), b"X=1\n").unwrap();
    commit_all(&repo, "init");
    let original = fs::read(repo.join(".gitattributes")).unwrap();
    let mut attributes = original.clone();
    attributes.extend_from_slice(b"[attr]transcrypt -text\ntranscrypt-v3-probe/probe filter=transcrypt-v3\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    fs::write(repo.join("a.env"), b"NEWSECRET\n").unwrap();
    run(&repo, "git", &["add", "-A"], None);
    let err = run_fails(&repo, "git", &["commit", "-qm", "spoof"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "-m", "spoof"], None);
    let err = run_fails(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
    assert!(err.contains("does not set filter=transcrypt-v3"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard", "HEAD~1"], None);
    // Amend: remove x.env in one commit, then amend it back in under an
    // lfs rule, unencrypted.
    run(&repo, "git", &["rm", "-q", "x.env"], None);
    run(&repo, "git", &["commit", "-qm", "remove x"], None);
    let mut attributes = original;
    attributes.extend_from_slice(b"x.env filter=lfs\n");
    fs::write(repo.join(".gitattributes"), attributes).unwrap();
    fs::write(repo.join("x.env"), b"X=plain\n").unwrap();
    run(&repo, "git", &["add", "-A"], None);
    let err = run_fails(&repo, "git", &["commit", "-q", "--amend", "--no-edit"], None);
    assert!(err.contains("x.env") && err.contains("`lfs`"), "{err}");
    run(&repo, "git", &["reset", "-q", "--hard"], None);

    // Eighth review: an amend that moves a record removed by `HEAD`, or
    // that keeps a raw move `HEAD` committed, is refused like the audit
    // refuses it: locked, and unlocked (an entry equal to `HEAD` is still
    // authenticated when `HEAD^1` differs).
    run(&repo, bin(), &["lock"], None);
    run(&repo, "git", &["checkout", "-q", "HEAD~1", "--", "x.env"], None);
    run(&repo, "git", &["mv", "x.env", "y.env"], None);
    let err = run_fails(&repo, "git", &["commit", "-q", "--amend", "--no-edit"], None);
    assert!(err.contains("y.env holds the encrypted x.env"), "{err}");
    run(&repo, "git", &["commit", "-q", "--no-verify", "--amend", "--no-edit"], None);
    run_fails(&repo, bin(), &["audit", "HEAD~1..HEAD"], None);
    run(&repo, bin(), &["unlock", "--password-stdin", "--no-hydrate"], Some(PASS));
    let err = run_fails(&repo, "git", &["commit", "-q", "--amend", "--no-edit", "-m", "amended"], None);
    assert!(err.contains("y.env"), "{err}");
}

/// What a `git` shim does to kill the `migrate` that runs it.
#[cfg(unix)]
const KILL: &str = "kill -9 $PPID; exit 1";

/// `migrate --password-stdin`, with a `git` (in the directory `shim`) on
/// PATH that runs the shell command `action` instead of the re-encryption
/// (`git add --renormalize`).
#[cfg(unix)]
fn migrate_with_shim(shim: &std::path::Path, repo: &std::path::Path, action: &str) -> std::process::Output {
    fs::create_dir_all(shim).unwrap();
    let real_git = String::from_utf8(run(repo, "sh", &["-c", "command -v git"], None)).unwrap();
    fs::write(shim.join("git"), format!("#!/bin/sh\ncase \"$*\" in *--renormalize*) {action};; esac\nexec {} \"$@\"\n",
        real_git.trim())).unwrap();
    make_executable(&shim.join("git"));
    let path = format!("{}:{}", shim.display(), std::env::var("PATH").unwrap());
    let mut child = Command::new(bin()).args(["migrate", "--password-stdin"]).current_dir(repo)
        .env("PATH", &path).stdin(Stdio::piped()).stdout(Stdio::null()).stderr(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(PASS).unwrap();
    child.wait_with_output().unwrap()
}

/// Seventh review F3: a resumed migration that fails again stays
/// resumable, and a third run completes it.
#[test]
#[cfg(unix)] // The interruption is a shell script named `git` on PATH.
#[cfg_attr(target_os = "openbsd", ignore = "Bash transcrypt (v2) needs `head -c`, which OpenBSD lacks")]
fn a_failed_resume_of_migrate_stays_resumable() {
    let mut scratch = Scratch::new("resume2");
    let repo = scratch.git_repo("repo");
    init_bash_v2(&repo);
    fs::write(repo.join(".gitattributes"), b"*.key filter=crypt diff=crypt merge=crypt\n").unwrap();
    fs::write(repo.join("a.key"), b"v2 secret\n").unwrap();
    commit_all(&repo, "v2");
    let shim = scratch.root.join("shim");
    assert!(!migrate_with_shim(&shim, &repo, KILL).status.success());
    let out = migrate_with_shim(&shim, &repo, "exit 1");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("rerun"), "{}", String::from_utf8_lossy(&out.stderr));
    assert!(repo.join(".transcrypt/config").exists(), "still resumable");
    run(&repo, bin(), &["migrate", "--password-stdin"], Some(PASS));
    assert!(is_record(&staged(&repo, "a.key")));
}

/// Committing an octopus merge stopped with `--no-commit`: the hook looks
/// up entries in both merged commits at once (paths repeat across them),
/// keeps their records as they are, and still seals a local addition.
#[test]
fn octopus_merges_check_every_incoming_commit() {
    let mut scratch = Scratch::new("octopus");
    let repo = scratch.repo("repo");
    for (branch, file) in [("one", "one.secret"), ("two", "two.secret")] {
        run(&repo, "git", &["checkout", "-q", "-b", branch, "main"], None);
        fs::write(repo.join(file), format!("{branch} plaintext\n")).unwrap();
        commit(&repo, &[file], branch);
    }
    run(&repo, "git", &["checkout", "-q", "main"], None);
    fs::write(repo.join("README"), b"diverged\n").unwrap();
    commit(&repo, &["README"], "diverge");
    run(&repo, "git", &["merge", "-q", "--no-commit", "one", "two"], None);
    assert_eq!(fs::read_to_string(repo.join(".git/MERGE_HEAD")).unwrap().lines().count(), 2);
    let blob = String::from_utf8(run(&repo, "git", &["hash-object", "-w", "--stdin"], Some(b"local plaintext\n"))).unwrap();
    run(&repo, "git", &["update-index", "--add", "--cacheinfo", &format!("{REGULAR_FILE_MODE},{},three.secret", blob.trim())], None);
    run(&repo, "git", &["commit", "-qm", "octopus"], None);
    assert_eq!(run(&repo, "git", &["rev-list", "--parents", "-1", "HEAD"], None).split(|b| *b == b' ').count(), 4);
    assert_eq!(committed(&repo, "one.secret"), run(&repo, "git", &["show", "one:one.secret"], None));
    assert_eq!(committed(&repo, "two.secret"), run(&repo, "git", &["show", "two:two.secret"], None));
    assert!(is_record(&committed(&repo, "three.secret")));
    run(&repo, bin(), &["verify-index"], None);
}
