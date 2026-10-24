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

use transcrypt_protocol::{base64_encode, detect_format, encode_v2, parse_v2, Format, V2Error};

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
fn openssl_inner(args: &[&str], stdin: &[u8], test_password: Option<&str>) -> Vec<u8> {
    let mut command = Command::new("openssl");
    command
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    // Legacy Bash uses -pass env:ENC_PASS. These test values are PUBLIC,
    // nonsecret fixtures. Do not use this test helper with real passwords.
    if let Some(pw) = test_password {
        command.env("ENC_PASS", pw);
    }
    let mut child = command
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

fn openssl(args: &[&str], stdin: &[u8]) -> Vec<u8> {
    openssl_inner(args, stdin, None)
}

fn openssl_with_test_password(args: &[&str], stdin: &[u8], password: &str) -> Vec<u8> {
    openssl_inner(args, stdin, Some(password))
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

    // 2. encrypt using the actual Bash filter's -pass env:ENC_PASS.
    // Do not write password fixtures to predictable paths in /tmp: the
    // earlier test could follow an attacker-planted symlink and overwrite
    // a file accessible to the test user.
    let ciphertext = openssl_with_test_password(
        &["enc", "-e", "-aes-256-cbc", "-md", "MD5", "-S", &salt_hex,
          "-pass", "env:ENC_PASS"],
        plaintext,
        password,
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
    assert_eq!(encode_v2(&rec).unwrap(), text);
    assert_eq!(detect_format(&text), Format::V2);

    // 5. decrypting the Rust-split ciphertext with the Bash pipeline
    //    recovers the plaintext
    let recovered = openssl_with_test_password(
        &["enc", "-d", "-aes-256-cbc", "-md", "MD5", "-S", &salt_hex,
          "-pass", "env:ENC_PASS"],
        &rec.ciphertext,
        password,
    );
    assert_eq!(&recovered[..], plaintext);

    // 6. an incomplete base64 group must fail structural parsing.
    // Other truncations can remain structurally valid for e.g. AES-CTR;
    // their detection belongs to authenticated crypto, absent in v2.
    let truncated = text[..29].to_vec();
    assert!(matches!(parse_v2(&truncated), Err(V2Error::Base64(_))));
    assert_eq!(detect_format(&truncated), Format::Invalid);

    // 7. stream ciphers in the released Bash tool do not have AES-CBC
    // padding. Confirm arbitrary positive ciphertext lengths are legal.
    let ctr_text = openssl_with_test_password(
        &["enc", "-e", "-aes-256-ctr", "-md", "MD5", "-S", &salt_hex,
          "-pass", "env:ENC_PASS"],
        plaintext,
        password,
    );
    assert_eq!(ctr_text.len(), plaintext.len());
    let mut ctr_binary = Vec::new();
    ctr_binary.extend_from_slice(b"Salted__");
    ctr_binary.extend_from_slice(&hex_to_bytes(&salt_hex));
    ctr_binary.extend_from_slice(&ctr_text);
    let ctr_encoded = openssl(&["base64"], &ctr_binary);
    let ctr_record = parse_v2(&ctr_encoded).expect("v2 AES-CTR is structurally valid");
    assert_eq!(ctr_record.ciphertext, ctr_text);
    assert_eq!(encode_v2(&ctr_record).unwrap(), ctr_encoded);

}

#[test]
fn base64_encoder_matches_openssl_across_line_boundaries() {
    if !openssl_available() {
        eprintln!("note: openssl unavailable; skipping wire encoder comparison");
        return;
    }
    for len in [0usize, 1, 2, 3, 4, 46, 47, 48, 49, 63, 64, 65, 128, 257] {
        let data: Vec<u8> = (0..len).map(|i| ((i * 61 + 73) % 256) as u8).collect();
        assert_eq!(
            base64_encode(&data),
            openssl(&["base64"], &data),
            "OpenSSL Base64 formatting differed at input length {len}"
        );
    }
}
