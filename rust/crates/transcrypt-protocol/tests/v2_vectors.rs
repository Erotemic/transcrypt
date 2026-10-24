//! Differential tests against the released Bash implementation's v2
//! encoding pipeline (see `transcrypt::git_clean`):
//!
//! ```text
//! salt  = last 16 hex chars of
//!         `openssl dgst -hmac "<path>:<password>" -sha256 <plaintext>`
//! blob  = "Salted__" || salt(8 bytes) ||
//!         openssl enc -e -aes-256-cbc -md MD5 -pass <password> -S <salt>
//! text  = openssl base64 of blob   (64-char lines, trailing newline)
//! ```
//!
//! These tests require `openssl` on `PATH`; they skip (do not fail)
//! where it is absent.

use std::io::Write;
use std::process::{Command, Stdio};

use transcrypt_protocol::{detect_format, parse_v2, Format, V2Error};

fn openssl_available() -> bool {
    Command::new("openssl")
        .arg("version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Run `openssl <args>` feeding `stdin`, returning the stdout bytes.
fn openssl(args: &[&str], stdin: &[u8]) -> Vec<u8> {
    let mut child = Command::new("openssl")
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("spawn openssl: {e}"));
    {
        let mut s = child.stdin.take().expect("stdin pipe");
        s.write_all(stdin)
            .expect("write stdin");
        // close stdin so openssl sees EOF
        drop(s);
    }
    let out = child
        .wait_with_output()
        .expect("wait openssl");
    assert!(
        out.status.success(),
        "openssl {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    out.stdout
}

fn hex_to_bytes(hex: &str) -> Vec<u8> {
    let b = hex.as_bytes();
    let mut v = Vec::with_capacity(b.len() / 2);
    let mut i = 0;
    while i < b.len() {
        let hi = (b[i] as char).to_digit(16).unwrap() as u8;
        let lo = (b[i + 1] as char).to_digit(16).unwrap() as u8;
        v.push((hi << 4) | lo);
        i += 2;
    }
    v
}

#[test]
fn v2_golden_structural() {
    if !openssl_available() {
        eprintln!("note: openssl not available; skipping v2 golden test");
        return;
    }
    let plaintext = b"top secret file contents\nline two\n";
    let password = "test-password-0001";
    let path = "secrets/notes.txt";

    // 1. derived salt, exactly as the Bash filter computes it
    let key = format!("{path}:{password}");
    let hmac = openssl(
        &["dgst", "-hmac", &key, "-sha256"],
        plaintext,
    );
    let line = String::from_utf8(hmac).unwrap();
    let hex = line.split('=').nth(1).expect("hmac output").trim().to_string();
    assert_eq!(hex.len(), 64, "HMAC-SHA256 is 64 hex chars");
    let salt_hex = hex[48..].to_string();

    // 2. encrypt the plaintext with the same openssl invocation the
    //    Bash filter makes (-pass from a file, like the real pipeline)
    let dir = std::env::temp_dir().join(format!(
        "transcrypt-rust-v2-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let pwfile = dir.join("pw");
    std::fs::write(&pwfile, password).unwrap();
    let ciphertext = openssl(
        &[
            "enc",
            "-e",
            "-aes-256-cbc",
            "-md",
            "MD5",
            "-S",
            &salt_hex,
            "-pass",
            &format!("file:{}", pwfile.display()),
        ],
        plaintext,
    );

    // 3. build the committed text: "Salted__" + salt + ciphertext,
    //    base64-wrapped at 64 columns
    let mut blob: Vec<u8> = Vec::new();
    blob.extend_from_slice(b"Salted__");
    blob.extend_from_slice(&hex_to_bytes(&salt_hex));
    blob.extend_from_slice(&ciphertext);
    let text = openssl(&["base64"], &blob);

    // 4. the Rust parser accepts what the Bash implementation produced
    let rec = parse_v2(&text).expect("Rust must parse Bash-produced v2");
    assert_eq!(
        &rec.salt[..],
        &hex_to_bytes(&salt_hex)[..],
        "salt must match the Bash-derived value"
    );
    assert_eq!(rec.ciphertext, ciphertext);
    assert_eq!(detect_format(&text), Format::V2);

    // 5. decrypting the Rust-split ciphertext with the Bash pipeline
    //    recovers the plaintext
    let recovered = openssl(
        &[
            "enc",
            "-d",
            "-aes-256-cbc",
            "-md",
            "MD5",
            "-S",
            &salt_hex,
            "-pass",
            &format!("file:{}", pwfile.display()),
        ],
        &rec.ciphertext,
    );
    assert_eq!(&recovered[..], plaintext);

    // 6. a truncated copy must fail closed
    let mut truncated = text.clone();
    truncated.truncate(truncated.len() / 2);
    assert!(
        matches!(
            parse_v2(&truncated),
            Err(V2Error::Base64(_))
                | Err(V2Error::BadCiphertextLength { .. })
                | Err(V2Error::BadBinaryMagic)
        ),
        "truncated v2 must not parse"
    );
    assert_eq!(
        detect_format(&truncated),
        Format::Invalid,
        "truncated v2 must never be classified as plaintext"
    );

    std::fs::remove_dir_all(&dir).ok();
}
