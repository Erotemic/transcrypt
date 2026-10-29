//! The Bash v2 implementation is a separate, executable reference.
//! These tests cross-check REAL Bash/OpenSSL output, Rust/OpenSSL output,
//! real Git clean filters, and legacy published ciphertext fixtures.
//! All passwords in this file are public synthetic test values.

use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

use transcrypt_protocol::{parse_v2, V2_BASE64_PREFIX};

const BASH_SOURCE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../transcrypt");
const RUST_BIN: &str = env!("CARGO_BIN_EXE_transcrypt-legacy");

struct Repo { dir: PathBuf }

impl Repo {
    fn new() -> Self {
        // The clock alone does not tell parallel tests apart (macOS keeps
        // microseconds), so each repository also takes the next number.
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let nano = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let dir = std::env::temp_dir().join(format!("transcrypt-legacy-parity-{}-{nano}-{n}", std::process::id()));
        std::fs::create_dir(&dir).unwrap();
        let repo = Repo { dir };
        repo.git(&["init", "-q"]);
        repo.config("user.name", "Transcrypt Test");
        repo.config("user.email", "test@example.invalid");
        repo.config("transcrypt.version", "2.3.2");
        repo.config("transcrypt.cipher", "aes-256-cbc");
        repo.config("transcrypt.password", "abc 123");
        repo.config("transcrypt.super-secret.cipher", "aes-256-cbc");
        repo.config("transcrypt.super-secret.password", "321cba");
        repo.config("transcrypt.openssl-path", "openssl");
        repo
    }
    fn git(&self, args: &[&str]) -> Vec<u8> {
        let out = Command::new("git").args(args).current_dir(&self.dir)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .output().unwrap();
        assert!(out.status.success(), "git {args:?} failed: {}", String::from_utf8_lossy(&out.stderr));
        out.stdout
    }
    fn config(&self, name: &str, value: &str) { self.git(&["config", "--local", name, value]); }
    fn file(&self, name: &str, bytes: &[u8]) {
        let path = self.dir.join(name);
        if let Some(parent) = path.parent() { std::fs::create_dir_all(parent).unwrap(); }
        std::fs::write(path, bytes).unwrap();
    }
    fn invoke(&self, program: &OsStr, args: &[OsString], input: &[u8]) -> Output {
        let mut child = Command::new(program)
            .args(args)
            .current_dir(&self.dir)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn().unwrap();
        let mut stdin = child.stdin.take().unwrap();
        let (write, result) = std::thread::scope(|scope| {
            let write = scope.spawn(move || { let r = stdin.write_all(input); drop(stdin); r });
            let result = child.wait_with_output().unwrap();
            (write.join().unwrap(), result)
        });
        // A command refused before it reads its input closes the pipe; its
        // exit status, not this write, is what the test checks.
        if let Err(e) = write { assert_eq!(e.kind(), std::io::ErrorKind::BrokenPipe, "{e}"); }
        Output { success: result.status.success(), stdout: result.stdout, stderr: result.stderr }
    }
    fn bash(&self, action: &str, args: &[&str], input: &[u8]) -> Output {
        let mut argv = vec![OsString::from(BASH_SOURCE), OsString::from(action)];
        argv.extend(args.iter().map(|item| OsString::from(*item)));
        self.invoke(OsStr::new("bash"), &argv, input)
    }
    fn rust(&self, action: &str, args: &[&str], input: &[u8]) -> Output {
        let mut argv = vec![OsString::from(action)];
        argv.extend(args.iter().map(|item| OsString::from(*item)));
        self.invoke(OsStr::new(RUST_BIN), &argv, input)
    }
}

impl Drop for Repo {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.dir); }
}

struct Output { success: bool, stdout: Vec<u8>, stderr: Vec<u8> }

fn equivalent_clean(repo: &Repo, file: &str, input: &[u8], ctx: Option<&str>) -> Vec<u8> {
    repo.file(file, input);
    let context_arg = ctx.map(|v| format!("context={v}"));
    let args: Vec<&str> = context_arg.as_deref().into_iter().chain(std::iter::once(file)).collect();
    let bash = repo.bash("clean", &args, input);
    let rust = repo.rust("clean", &args, input);
    assert!(bash.success, "Bash clean failed: {}", String::from_utf8_lossy(&bash.stderr));
    assert!(rust.success, "Rust clean failed: {}", String::from_utf8_lossy(&rust.stderr));
    assert_eq!(rust.stdout, bash.stdout, "clean ciphertext disagreement for {file:?}");
    rust.stdout
}

#[test]
fn published_golden_objects_and_contexts() {
    let repo = Repo::new();
    let input = b"My secret content\n";
    let default = equivalent_clean(&repo, "sensitive_file", input, None);
    assert_eq!(default, b"U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwbgVd48WaQXznsg42nXbQrlWsf/qiCg\n");
    let named = equivalent_clean(&repo, "super_sensitive_file", input, Some("super-secret"));
    assert_eq!(named, b"U2FsdGVkX1+dAkIV/LAKXMmqjDNOGoOVK8Rmhw9tUnbR4dwBDglpkXIT3yzYBvoc\n");
    for (encrypted, ctx) in [(&default[..], None), (&named[..], Some("super-secret"))] {
        let context_arg = ctx.map(|v| format!("context={v}"));
        let args: Vec<&str> = context_arg.as_deref().into_iter().collect();
        let bash = repo.bash("smudge", &args, encrypted);
        let rust = repo.rust("smudge", &args, encrypted);
        assert!(bash.success && rust.success);
        assert_eq!(bash.stdout, input);
        assert_eq!(rust.stdout, input);
    }
}

#[test]
fn binary_utf8_large_and_empty() {
    let repo = Repo::new();
    for (name, content) in [
        ("folder/notes ünicode", b"with UTF-8 paths\n".to_vec()),
        ("binary", vec![0, 255, 1, 10, 13, 0, 17, 128]),
        ("big-file", (0..262_144).map(|i| ((i * 53 + 19) % 256) as u8).collect()),
        ("empty", Vec::new()),
    ] {
        let ciphertext = equivalent_clean(&repo, name, &content, None);
        if !content.is_empty() {
            assert!(ciphertext.starts_with(V2_BASE64_PREFIX));
            parse_v2(&ciphertext).unwrap();
        }
        let rust = repo.rust("smudge", &[], &ciphertext);
        assert!(rust.success, "smudge failed for {name}");
        assert_eq!(rust.stdout, content);
    }
}

#[test]
fn empty_worktree_file_does_not_bypass_nonempty_stdin() {
    let repo = Repo::new();
    repo.file("changed", b"");
    let plain = b"actual staged content\n";
    let bash = repo.bash("clean", &["changed"], plain);
    let rust = repo.rust("clean", &["changed"], plain);
    assert!(bash.success && rust.success);
    assert_eq!(bash.stdout, rust.stdout);
    assert!(rust.stdout.starts_with(V2_BASE64_PREFIX));
}

#[test]
fn missing_future_crypto_must_not_downgrade_to_v2() {
    let repo = Repo::new();
    let future_record = b"TCRYPT3:placeholder";
    repo.file("secret", future_record);
    for action in ["clean", "smudge"] {
        let args = if action == "clean" { vec!["secret"] } else { Vec::new() };
        let bash = repo.bash(action, &args, future_record);
        let rust = repo.rust(action, &args, future_record);
        assert!(!bash.success && !rust.success);
        assert!(bash.stdout.is_empty() && rust.stdout.is_empty());
    }
}

#[test]
fn git_index_uses_rust_filter_and_bash_can_decrypt() {
    let repo = Repo::new();
    repo.file(".gitattributes", b"sensitive_file filter=crypt diff=crypt\n");
    repo.file("sensitive_file", b"My secret content\n");
    let quoted_bin = format!("'{}'", RUST_BIN.replace('\'', "'\\''"));
    repo.config("filter.crypt.clean", &format!("{quoted_bin} clean %f"));
    repo.config("filter.crypt.smudge", &format!("{quoted_bin} smudge"));
    repo.config("filter.crypt.required", "true");
    repo.git(&["add", ".gitattributes", "sensitive_file"]);
    let committed_blob = repo.git(&["show", ":sensitive_file"]);
    assert_eq!(committed_blob, b"U2FsdGVkX1/6ilR0PmJpAyCF7iG3+k4aBwbgVd48WaQXznsg42nXbQrlWsf/qiCg\n");
    let out = repo.bash("smudge", &[], &committed_blob);
    assert!(out.success);
    assert_eq!(out.stdout, b"My secret content\n");
}

#[test]
fn invalid_context_and_unimplemented_operations_fail() {
    let repo = Repo::new();
    for args in [vec!["context=a--b", "file"], vec!["context=A", "file"]] {
        let out = repo.rust("clean", &args, b"SECRET");
        assert!(!out.success);
        assert!(out.stdout.is_empty());
    }
    let out = repo.rust("--migrate-v3", &[], b"");
    assert!(!out.success);
    assert!(out.stdout.is_empty());
}

#[cfg(unix)]
#[test]
#[cfg_attr(target_os = "macos", ignore = "APFS refuses file names that are not UTF-8")]
fn non_utf8_git_path_has_same_legacy_salt() {
    use std::os::unix::ffi::OsStringExt;
    let repo = Repo::new();
    let filename = OsString::from_vec(vec![b'n', b'a', b'm', b'e', b'-', 0xff]);
    let path = repo.dir.join(PathBuf::from(filename.clone()));
    std::fs::write(&path, b"opaque pathname bytes\n").unwrap();
    let bash_args = [
        OsString::from(BASH_SOURCE),
        OsString::from("clean"),
        filename.clone(),
    ];
    let rust_args = [OsString::from("clean"), filename];
    let bash = repo.invoke(OsStr::new("bash"), &bash_args, b"opaque pathname bytes\n");
    let rust = repo.invoke(OsStr::new(RUST_BIN), &rust_args, b"opaque pathname bytes\n");
    assert!(bash.success && rust.success);
    assert_eq!(rust.stdout, bash.stdout);
}
