//! A Rust *alternative filter* for existing Bash-initialized v2 repositories.
//! It does not reconfigure Git, manage secrets, or claim secure v3 support.

use std::ffi::OsString;
use std::io::{Read, Write};
use std::path::PathBuf;

use transcrypt_legacy::{clean, load_settings, path_bytes, smudge, textconv, LegacyError};

fn fail(message: &str) -> ! {
    eprintln!("transcrypt-rs: {message}");
    std::process::exit(1)
}

fn run() -> Result<Vec<u8>, LegacyError> {
    let mut args: Vec<OsString> = std::env::args_os().skip(1).collect();
    if args.is_empty() { return Err(LegacyError::Unsupported("use clean, smudge, textconv, --version, or --help")); }
    let operation = args.remove(0);
    if operation.to_str() == Some("--help") || operation.to_str() == Some("-h") {
        return Ok(b"transcrypt-rs: legacy v2 alternative Git filters\nusage: transcrypt-rs clean [context=NAME] PATH\n       transcrypt-rs smudge [context=NAME]\n       transcrypt-rs textconv [context=NAME] PATH\n       transcrypt-rs --version\nInitialization, rekey, migration and secure v3 are not yet supported.\n".to_vec());
    }
    if operation.to_str() == Some("--version") {
        return Ok(b"transcrypt-rs 0.1.0 (legacy v2 compatibility)\n".to_vec());
    }
    let operation = operation.to_str().ok_or(LegacyError::Unsupported("non-UTF8 operation"))?;
    if !["clean", "smudge", "textconv"].contains(&operation) {
        return Err(LegacyError::Unsupported("operation not implemented; no Bash fallback"));
    }
    let mut context = "default".to_string();
    if let Some(first) = args.first().and_then(|a| a.to_str()) {
        if let Some(name) = first.strip_prefix("context=") {
            context = name.to_owned();
            args.remove(0);
        }
    }
    let settings = load_settings(&context)?;
    let mut data = Vec::new();
    if operation == "textconv" {
        if args.len() != 1 { return Err(LegacyError::Unsupported("textconv expects one path")); }
        data = std::fs::read(PathBuf::from(args[0].clone()))?;
        return textconv(&settings, &data);
    }
    std::io::stdin().read_to_end(&mut data)?;
    if operation == "smudge" {
        if !args.is_empty() { return Err(LegacyError::Unsupported("smudge accepts no path")); }
        return smudge(&settings, &data);
    }
    if args.len() != 1 { return Err(LegacyError::Unsupported("clean expects one path")); }
    clean(&settings, &path_bytes(&args[0])?, &data)
}

fn main() {
    match run() {
        Ok(bytes) => {
            if let Err(e) = std::io::stdout().write_all(&bytes) {
                fail(&format!("stdout write failed: {e}"));
            }
        }
        Err(e) => fail(&e.to_string()),
    }
}
