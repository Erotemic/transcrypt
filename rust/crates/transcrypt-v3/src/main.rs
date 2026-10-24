//! Git integration adapter. This adapter uses OS/Git effects and is outside
//! the current Aeneas pure-core proof boundary.
#[cfg(not(unix))]
compile_error!("transcrypt-v3 POC requires Unix for 0600/0700 local credential permissions");

use std::{
    env, fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};
#[cfg(unix)]
use std::os::unix::{ffi::OsStringExt, fs::OpenOptionsExt};
use zeroize::Zeroizing;
use transcrypt_v3::{
    authenticate_config, decrypt_file, encrypt_file, initialize_config, unlock_config, SecretKey,
    KEY_SIZE, MAX_FILE,
};
use transcrypt_v3_core::{parse_file_header, FILE_MIN_LEN, SALT_LEN};

const ATTRS: &[u8] = b"*.secret filter=transcrypt-v3 -diff\n";
const KEY_FILE_NAME: &str = "key";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("transcrypt-v3: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let action = args.first().ok_or("usage: transcrypt-v3 init|unlock|lock|clean|smudge|verify-index|hydrate [--password-stdin]")?;
    if args.len() > 2 || (args.len() == 2 && args[1] != "--password-stdin") {
        return Err("unexpected arguments; only --password-stdin is supported for init/unlock".into());
    }
    if args.len() == 2 && action != "init" && action != "unlock" {
        return Err("--password-stdin only applies to init/unlock".into());
    }
    let root = repo_root()?;
    match action.as_str() {
        "init" => init(&root, passphrase(args.len() == 2)?),
        "unlock" => unlock(&root, passphrase(args.len() == 2)?),
        "lock" => lock(&root),
        "clean" => filter(&root, true),
        "smudge" => filter(&root, false),
        "verify-index" => verify_index(&root),
        "hydrate" => hydrate(&root),
        _ => Err("unknown operation; v3 supports only init/unlock/lock/clean/smudge/verify-index/hydrate".into()),
    }
}

fn output(mut command: Command) -> Result<Vec<u8>, String> {
    let desc = format!("{:?}", command);
    let result = command.output().map_err(|e| format!("cannot run {desc}: {e}"))?;
    if !result.status.success() {
        return Err(format!("Git command failed ({desc}): {}", String::from_utf8_lossy(&result.stderr)));
    }
    Ok(result.stdout)
}

fn git(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = Command::new("git");
    command.current_dir(root).args(arguments);
    output(command)
}

fn repo_root() -> Result<PathBuf, String> {
    let mut command = Command::new("git");
    command.args(["rev-parse", "--show-toplevel"]);
    let bytes = output(command)?;
    let root = PathBuf::from(String::from_utf8(bytes).map_err(|_| "repository path is not UTF-8")?.trim());
    if !root.is_dir() {
        return Err("Git repository root is not a directory".into());
    }
    let git_dir = root.join(".git");
    let meta = fs::symlink_metadata(&git_dir).map_err(|_| "only normal Git checkouts with a .git directory are supported")?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err("linked worktrees and symlinked .git directories are not yet supported".into());
    }
    Ok(root)
}

fn config_path(root: &Path) -> Result<PathBuf, String> {
    let dir = root.join(".transcrypt");
    let meta = fs::symlink_metadata(&dir).map_err(|_| "missing .transcrypt directory: run init or clone a v3 repository")?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err("unsafe .transcrypt directory".into());
    }
    let file = dir.join("config");
    let fmeta = fs::symlink_metadata(&file).map_err(|_| "missing committed .transcrypt/config")?;
    if !fmeta.is_file() || fmeta.file_type().is_symlink() {
        return Err("unsafe .transcrypt/config type".into());
    }
    Ok(file)
}

fn load_config(root: &Path) -> Result<Vec<u8>, String> {
    let bytes = fs::read(config_path(root)?).map_err(|e| format!("cannot read v3 config: {e}"))?;
    transcrypt_v3_core::parse_config(&bytes).map_err(|_| "invalid v3 config grammar")?;
    Ok(bytes)
}

fn key_dir(root: &Path) -> Result<PathBuf, String> {
    let path = root.join(".git/transcrypt-v3");
    if let Ok(meta) = fs::symlink_metadata(&path) {
        if !meta.is_dir() || meta.file_type().is_symlink() {
            return Err("unsafe local key directory".into());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if meta.permissions().mode() & 0o077 != 0 {
                return Err("local key directory permissions must be 0700".into());
            }
        }
    }
    Ok(path)
}

fn key_file(root: &Path) -> Result<PathBuf, String> {
    Ok(key_dir(root)?.join(KEY_FILE_NAME))
}

fn read_key(root: &Path, config: &[u8]) -> Result<SecretKey, String> {
    let file = key_file(root)?;
    let meta = fs::symlink_metadata(&file).map_err(|_| "repository locked: run transcrypt-v3 unlock")?;
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err("unsafe local key file".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if meta.permissions().mode() & 0o077 != 0 {
            return Err("key file permissions must be 0600".into());
        }
    }
    let bytes = Zeroizing::new(fs::read(&file).map_err(|_| "cannot read local key file")?);
    if bytes.len() != KEY_SIZE {
        return Err("incorrect local key length".into());
    }
    let mut key = Zeroizing::new([0u8; KEY_SIZE]);
    key.copy_from_slice(&bytes);
    authenticate_config(config, &key)?;
    Ok(key)
}

fn write_key(root: &Path, key: &SecretKey) -> Result<(), String> {
    let dir = key_dir(root)?;
    if !dir.exists() {
        fs::create_dir(&dir).map_err(|e| format!("cannot create local key directory: {e}"))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700))
                .map_err(|e| format!("cannot protect local key directory: {e}"))?;
        }
    }
    let path = dir.join(KEY_FILE_NAME);
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o600);
    let mut out = options.open(&path).map_err(|e| format!("key already unlocked or unsafe key path: {e}"))?;
    if let Err(e) = out.write_all(&key[..]).and_then(|_| out.sync_all()) {
        let _ = fs::remove_file(&path);
        return Err(format!("cannot persist local key: {e}"));
    }
    Ok(())
}

fn passphrase(from_stdin: bool) -> Result<Zeroizing<Vec<u8>>, String> {
    let bytes = if from_stdin {
        let mut value = Vec::new();
        io::stdin().take(4097).read_to_end(&mut value).map_err(|_| "cannot read passphrase from stdin")?;
        if value.len() > 4096 {
            return Err("passphrase too long".into());
        }
        if value.last() == Some(&b'\n') { value.pop(); }
        if value.last() == Some(&b'\r') { value.pop(); }
        value
    } else {
        rpassword::prompt_password("Transcrypt v3 passphrase: ")
            .map_err(|e| format!("cannot read terminal passphrase: {e}"))?
            .into_bytes()
    };
    if bytes.len() < 16 { return Err("v3 requires a passphrase of at least 16 bytes".into()); }
    Ok(Zeroizing::new(bytes))
}

fn shell_quote(text: &str) -> String {
    format!("'{}'", text.replace('\'', "'\\''"))
}

fn install_filters(root: &Path) -> Result<(), String> {
    let bin = env::current_exe().map_err(|_| "cannot resolve current executable")?;
    let path = bin.to_str().ok_or("executable path must be UTF-8")?;
    let program = shell_quote(path);
    for (k, value) in [
        ("filter.transcrypt-v3.clean", format!("{program} clean")),
        ("filter.transcrypt-v3.smudge", format!("{program} smudge")),
        ("filter.transcrypt-v3.required", "true".into()),
    ] {
        git(root, &["config", "--local", k, &value])?;
    }
    Ok(())
}

fn expected_hook() -> Result<String, String> {
    let bin = env::current_exe().map_err(|_| "cannot locate executable")?;
    let b = bin.to_str().ok_or("executable path must be UTF-8")?;
    Ok(format!("#!/bin/sh\nexec {} verify-index\n", shell_quote(b)))
}

fn check_hook_available(root: &Path) -> Result<(), String> {
    let path = root.join(".git/hooks/pre-commit");
    match fs::symlink_metadata(&path) {
        Ok(meta) => {
            if !meta.is_file() || meta.file_type().is_symlink() ||
                fs::read_to_string(&path).map_err(|_| "cannot read existing pre-commit hook")? != expected_hook()? {
                return Err("pre-commit hook already exists and is not this v3 hook; refuse to override".into());
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(_) => return Err("cannot inspect hook directory".into()),
    }
    Ok(())
}

fn install_hook(root: &Path) -> Result<(), String> {
    let path = root.join(".git/hooks/pre-commit");
    if path.exists() { return check_hook_available(root); }
    let script = expected_hook()?;
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o700);
    options.open(path).map_err(|e| format!("cannot install hook: {e}"))?
        .write_all(script.as_bytes()).map_err(|e| format!("cannot write hook: {e}"))?;
    Ok(())
}

fn init(root: &Path, password: Zeroizing<Vec<u8>>) -> Result<(), String> {
    let dir = root.join(".transcrypt");
    if fs::symlink_metadata(&dir).is_ok() {
        return Err(".transcrypt directory already exists; init requires a fresh v3 setup".into());
    }
    if fs::symlink_metadata(root.join(".gitattributes")).is_ok() {
        return Err(".gitattributes already exists; this POC requires a new attributes policy".into());
    }
    check_hook_available(root)?;
    if key_file(root)?.exists() { return Err("already unlocked".into()); }
    let mut salt = [0u8; SALT_LEN];
    getrandom::fill(&mut salt).map_err(|_| "OS randomness unavailable")?;
    let (config, key) = initialize_config(&password, &salt)?;
    fs::create_dir(&dir).map_err(|e| format!("cannot create .transcrypt: {e}"))?;
    let path = dir.join("config");
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    options.open(path).map_err(|e| format!("cannot create config: {e}"))?
        .write_all(&config).map_err(|e| format!("cannot write config: {e}"))?;
    fs::write(root.join(".gitattributes"), ATTRS)
        .map_err(|e| format!("cannot write attributes: {e}"))?;
    write_key(root, &key)?;
    install_filters(root)?;
    install_hook(root)?;
    git(root, &["add", "--", ".transcrypt/config", ".gitattributes"])?;
    eprintln!("Initialized v3; committed public metadata is required. Local key is stored in .git/transcrypt-v3/key until lock.");
    Ok(())
}

fn unlock(root: &Path, password: Zeroizing<Vec<u8>>) -> Result<(), String> {
    let config = load_config(root)?;
    if key_file(root)?.exists() { return Err("already unlocked; run lock before unlocking again".into()); }
    let key = unlock_config(&password, &config)?; // Authenticate BEFORE any persistent writes.
    check_hook_available(root)?;
    write_key(root, &key)?;
    install_filters(root)?;
    install_hook(root)?;
    eprintln!("Unlocked v3 locally. For fresh clones run `transcrypt-v3 hydrate` to materialize protected worktree files.");
    Ok(())
}

fn lock(root: &Path) -> Result<(), String> {
    // Every tracked secret must match the encrypted index BEFORE any worktree rewrite.
    // If anything is dirty or untracked, do not remove credentials.
    verify_index(root)?;
    let untracked = git(root, &["ls-files", "--others", "-z"])?;
    if untracked.split(|b| *b == 0).any(protected_path) {
        return Err("untracked *.secret files exist; refusing to leave unprotected plaintext behind".into());
    }
    let config = load_config(root)?;
    let key = read_key(root, &config)?;
    let mut to_flush = Vec::new();
    for (mode, path) in indexed_files(root)? {
        if !protected_path(&path) { continue; }
        if mode != b"100644" {
            return Err("protected staged object is not a regular file".into());
        }
        let relative = indexed_path(&path)?;
        let dest = root.join(relative);
        require_regular_file(&dest)?;
        let source = read_limited(fs::File::open(&dest)
            .map_err(|_| "cannot read protected worktree file")?, MAX_FILE + FILE_MIN_LEN)?;
        let object = git_show(root, &path)?;
        if source == object { continue; }
        let derived = encrypt_file(&config, &key, &source)?;
        if derived != object {
            return Err("protected worktree has uncommitted plaintext changes; refusing lock".into());
        }
        to_flush.push((dest, object));
    }
    // Write only ciphertext using exclusive temporary files and atomic rename.
    // A filesystem crash can still leave a partially flushed worktree; keep the
    // key until all renames succeed, and do not claim secure disk erasure.
    for (i, (dest, object)) in to_flush.iter().enumerate() {
        let temp = dest.with_file_name(format!(".transcrypt-v3-lock-{}-{i}.tmp", std::process::id()));
        let mut opts = fs::OpenOptions::new();
        opts.write(true).create_new(true);
        #[cfg(unix)]
        opts.mode(0o600);
        let mut f = opts.open(&temp).map_err(|e| format!("cannot create encrypted temporary file: {e}"))?;
        if let Err(e) = f.write_all(object).and_then(|_| f.sync_all()) {
            let _ = fs::remove_file(&temp);
            return Err(format!("cannot write encrypted temporary file: {e}"));
        }
        fs::rename(&temp, dest).map_err(|e| format!("cannot replace protected file: {e}"))?;
    }
    fs::remove_file(key_file(root)?).map_err(|e| format!("cannot remove local key: {e}"))?;
    eprintln!("Locked: tracked *.secret files flushed to ciphertext and local key removed. This does not securely erase historical plaintext backups.");
    Ok(())
}

fn read_limited<R: Read>(read: R, limit: usize) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    read.take((limit as u64) + 1).read_to_end(&mut out).map_err(|_| "cannot read input")?;
    if out.len() > limit { return Err("v3 filter input exceeds supported size".into()); }
    Ok(out)
}

fn filter(root: &Path, clean: bool) -> Result<(), String> {
    let config = load_config(root)?;
    let key = read_key(root, &config)?;
    let input = read_limited(io::stdin(), MAX_FILE + FILE_MIN_LEN)?;
    let result = if clean {
        if parse_file_header(&input).is_ok() {
            return Err("worktree contains v3 ciphertext instead of plaintext; refusing double encryption".into());
        }
        encrypt_file(&config, &key, &input)?
    } else {
        decrypt_file(&config, &key, &input)?
    };
    io::stdout().write_all(&result).map_err(|_| "cannot write output")?;
    Ok(())
}

fn git_show(root: &Path, path: &[u8]) -> Result<Vec<u8>, String> {
    let mut query = Vec::with_capacity(path.len() + 1);
    query.push(b':');
    query.extend_from_slice(path);
    let mut command = Command::new("git");
    command.current_dir(root).arg("show");
    #[cfg(unix)]
    command.arg(std::ffi::OsString::from_vec(query));
    #[cfg(not(unix))]
    command.arg(String::from_utf8(query).map_err(|_| "non-UTF8 path unsupported here")?);
    output(command)
}

fn indexed_path(path: &[u8]) -> Result<PathBuf, String> {
    #[cfg(unix)]
    let relative = PathBuf::from(std::ffi::OsString::from_vec(path.to_vec()));
    #[cfg(not(unix))]
    let relative = PathBuf::from(String::from_utf8(path.to_vec()).map_err(|_| "non-UTF8 path unsupported")?);
    if relative.is_absolute() || relative.components().any(|c| matches!(c, std::path::Component::ParentDir | std::path::Component::RootDir)) {
        return Err("unsafe protected relative path".into());
    }
    Ok(relative)
}

fn require_regular_file(path: &Path) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|_| "protected worktree file missing")?;
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err("protected worktree path must be a regular file, not a symlink".into());
    }
    Ok(())
}

/// Stage-0 files with paths represented as raw bytes (no newline splitting).
fn indexed_files(root: &Path) -> Result<Vec<(Vec<u8>, Vec<u8>)>, String> {
    let data = git(root, &["ls-files", "--stage", "-z"])?;
    let mut entries = Vec::new();
    for entry in data.split(|b| *b == 0).filter(|item| !item.is_empty()) {
        let tab = entry.iter().position(|x| *x == b'\t').ok_or("malformed Git index entry")?;
        let mode = &entry[..tab];
        if !mode.ends_with(b" 0") { return Err("unmerged index entries are unsupported".into()); }
        if mode.len() < 6 { return Err("malformed Git file mode".into()); }
        let mode = mode[..6].to_vec();
        entries.push((mode, entry[tab + 1..].to_vec()));
    }
    Ok(entries)
}

fn protected_path(path: &[u8]) -> bool {
    path.rsplit(|x| *x == b'/').next().unwrap_or(path).ends_with(b".secret")
}

fn verify_index(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    if git_show(root, b".transcrypt/config")? != config {
        return Err("staged .transcrypt/config is missing or differs from worktree".into());
    }
    if git_show(root, b".gitattributes")? != ATTRS {
        return Err("staged .gitattributes differs from required v3 policy".into());
    }
    let key = read_key(root, &config)?;
    for (mode, path) in indexed_files(root)? {
        if !protected_path(&path) { continue; }
        if mode != b"100644" {
            return Err("protected path is not a regular file in staged index".into());
        }
        let encrypted = git_show(root, &path)?;
        decrypt_file(&config, &key, &encrypted)?;
    }
    Ok(())
}

fn hydrate(root: &Path) -> Result<(), String> {
    let config = load_config(root)?;
    let key = read_key(root, &config)?;
    let entries: Vec<_> = indexed_files(root)?.into_iter().filter(|(_, path)| protected_path(path)).collect();
    // Preflight ALL paths before changing any working files.
    for (mode, path) in &entries {
        if mode != b"100644" { return Err("protected path is not regular".into()); }
        let object = git_show(root, path)?;
        decrypt_file(&config, &key, &object)?;
        let relative = indexed_path(path)?;
        require_regular_file(&root.join(&relative))?;
        if fs::read(root.join(relative)).map_err(|_| "missing worktree ciphertext; refusing overwrite")? != object {
            return Err("protected worktree changed; refusing destructive hydrate".into());
        }
    }
    for (_, path) in entries {
        let mut command = Command::new("git");
        command.current_dir(root).args(["restore", "--source=HEAD", "--worktree", "--"]);
        #[cfg(unix)]
        command.arg(std::ffi::OsString::from_vec(path));
        #[cfg(not(unix))]
        command.arg(String::from_utf8(path).map_err(|_| "non-UTF8 path unsupported")?);
        output(command)?;
    }
    eprintln!("Hydration complete.");
    Ok(())
}
