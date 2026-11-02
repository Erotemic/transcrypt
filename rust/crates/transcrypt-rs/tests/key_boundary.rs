//! The key boundary of the adapter (assumption A17): outside `lib.rs`, no
//! code builds primitives, authenticates a key or seals and opens records
//! itself. Every file operation goes through `ValidatedKey`, whose only
//! constructors are the verified `authenticate_key` and `unlock_stored_key`
//! (and whose fields are private: see its `compile_fail` doc test).

use std::{fs, path::Path};

/// The crate items that pair key material with a configuration, or use
/// such a pairing, without `ValidatedKey`.
const KEY_LEVEL: [&str; 10] = [
    "Keyed", "V3Primitives", "V3KeySchedule", "derive_key", "seal_record", "open_record",
    "authenticate_config", "authenticate_key", "unlock_stored_key", "initialize_config",
];

/// Whether `name` occurs in `line` as a whole identifier.
fn names(line: &str, name: &str) -> bool {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    line.match_indices(name).any(|(at, _)| {
        !line[..at].ends_with(ident) && !line[at + name.len()..].starts_with(ident)
    })
}

#[test]
fn only_the_library_touches_key_material() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut checked = 0;
    for entry in fs::read_dir(&src).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "rs") || path.file_name().is_some_and(|n| n == "lib.rs") {
            continue;
        }
        let text = fs::read_to_string(&path).unwrap();
        for (n, line) in text.lines().enumerate() {
            // Comments may name the verified functions.
            let code = line.split("//").next().unwrap_or_default();
            for name in KEY_LEVEL {
                assert!(!names(code, name), "{}:{}: uses `{name}` outside ValidatedKey", path.display(), n + 1);
            }
        }
        checked += 1;
    }
    assert!(checked > 1, "no adapter sources found in {}", src.display());
}
