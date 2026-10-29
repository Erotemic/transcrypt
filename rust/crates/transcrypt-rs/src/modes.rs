//! Unix permission bits, shared by every platform: the Unix adapters pass
//! them to the OS, and the Windows adapter reads "private" from the same
//! group/other bits.

/// Read and write for the owner only: key files, private plaintext, staging
/// files and the agent socket.
pub(crate) const PRIVATE_FILE: u32 = 0o600;
/// Owner-only access: private directories and hooks (run by this user).
pub(crate) const PRIVATE_DIR: u32 = 0o700;
/// The owner's read, write and execute bits.
#[cfg(unix)]
pub(crate) const OWNER_BITS: u32 = 0o700;
/// The group and other permission bits; none set means private to the owner.
pub(crate) const GROUP_OTHER_BITS: u32 = 0o077;
/// All read, write and execute bits (no setuid, setgid or sticky).
#[cfg(unix)]
pub(crate) const PERMISSION_BITS: u32 = 0o777;
/// Any execute bit: Git runs a hook only if one is set.
#[cfg(unix)]
pub(crate) const EXECUTE_BITS: u32 = 0o111;
/// The mode Git and the OS give an ordinary new file, before the umask.
pub(crate) const NEW_FILE: u32 = 0o666;
/// The mode for an ordinary new directory, before the umask.
pub(crate) const NEW_DIR: u32 = 0o777;
