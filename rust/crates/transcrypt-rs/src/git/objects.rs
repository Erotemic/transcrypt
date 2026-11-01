//! Blob reads by verified object id, through one `git cat-file --batch` per
//! `Repository`.

use super::*;

/// A Git object id that the verified core accepted (`is_object_id`: 40 or
/// 64 lowercase hexadecimal digits); `new` is the only way to make one.
/// Objects are read only by such an id, never by revision syntax such as
/// `:path`, which reads `:0:x.secret` as stage 0 of `x.secret`, or by text
/// that Git could read as an option.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) struct ObjectId(String);

impl ObjectId {
    /// `bytes` as an object id, if the verified core accepts them as one.
    pub(crate) fn new(bytes: &[u8]) -> Option<ObjectId> {
        // Hexadecimal digits: the conversion is exact.
        is_object_id(bytes).then(|| ObjectId(String::from_utf8_lossy(bytes).into_owned()))
    }

    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for ObjectId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Read at most a v3 record's worth of bytes, into wiped memory.
pub(crate) fn read_record(mut read: impl Read) -> Result<Zeroizing<Vec<u8>>, String> {
    read_wiped(&mut read, MAX_RECORD).map_err(|e| match e {
        ReadError::Failed => "cannot read input".into(),
        ReadError::TooLarge => too_large(),
    })
}

/// The content of one Git blob, named by its verified id. Reads stop at the v3 size bound, so a hostile oversized
/// blob is refused without being loaded. All reads of one `Repository`
/// share a single `git cat-file --batch`.
pub(crate) fn git_blob(repo: &Repository, oid: &ObjectId) -> Result<Vec<u8>, String> {
    read_blob(repo, oid, false)?.ok_or_else(too_large)
}

/// Like `git_blob`, but `None` for a blob larger than any v3 record (an
/// ordinary large file, which cannot be a record), skipped unread.
pub(crate) fn git_blob_if_record_sized(repo: &Repository, oid: &ObjectId) -> Result<Option<Vec<u8>>, String> {
    read_blob(repo, oid, true)
}

/// Whether blob `oid` has the v3 record envelope of the config `id`. Only
/// its size and first `ENVELOPE_PREFIX_LEN` bytes are read, which decide the
/// envelope exactly as the whole blob would (`record_envelope_prefix_ok`);
/// the rest is skipped unread.
pub(crate) fn is_record(repo: &Repository, oid: &ObjectId, id: &[u8; transcrypt_v3_core::ID_LEN]) -> Result<bool, String> {
    let prefix = with_objects(repo, |objects| objects.blob_prefix(oid))?;
    Ok(prefix.is_some_and(|(size, prefix)| record_envelope_prefix_ok(size, &prefix, id)))
}

fn read_blob(repo: &Repository, oid: &ObjectId, skip_large: bool) -> Result<Option<Vec<u8>>, String> {
    with_objects(repo, |objects| objects.blob(oid, skip_large))
}

/// Run `read` on the object reader of `repo`.
fn with_objects<T>(repo: &Repository, read: impl FnOnce(&mut Objects) -> Result<T, String>) -> Result<T, String> {
    let mut slot = repo.objects.borrow_mut();
    let result = get_or_try_init(&mut slot, || Objects::open(&repo.root)).and_then(read);
    if result.is_err() {
        // The stream may be out of step; never reuse it.
        *slot = None;
    }
    result
}

/// A `git cat-file --batch` reply that ended early.
const TRUNCATED_REPLY: &str = "truncated git cat-file reply";
/// A `git cat-file --batch` reply whose content is not followed by LF.
const MALFORMED_REPLY: &str = "malformed git cat-file reply";

/// One `git cat-file --batch` process. Each reply must be exactly
/// `<oid> blob <size> LF`, with `<size>` in canonical decimal, followed by
/// `<size>` bytes and LF; anything else (a missing object, another type, a
/// different id, a malformed or oversized header) is an error, so bytes can
/// never be attributed to the wrong object.
pub(super) struct Objects {
    child: std::process::Child,
    input: Option<std::process::ChildStdin>,
    output: io::BufReader<std::process::ChildStdout>,
}

impl Objects {
    fn open(root: &Path) -> Result<Objects, String> {
        let mut child = git_command_in(Some(root))
            .args(["cat-file", "--batch"])
            .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null())
            .spawn().map_err(|e| format!("cannot run git cat-file: {e}"))?;
        let input = child.stdin.take().ok_or("git cat-file input pipe missing")?;
        let output = child.stdout.take().ok_or("git cat-file output pipe missing")?;
        Ok(Objects { child, input: Some(input), output: io::BufReader::new(output) })
    }

    /// Ask for `oid` and read the header of the reply, which the verified
    /// core checks: the blob's size.
    fn request(&mut self, oid: &ObjectId) -> Result<u64, String> {
        use io::BufRead;
        let input = self.input.as_mut().ok_or("Git object reader closed")?;
        sigpipe_blocked(input, |input| input.write_all(format!("{oid}\n").as_bytes()).and_then(|_| input.flush()))
            .map_err(|_| "cannot query git cat-file")?;
        let mut header = Vec::new();
        (&mut self.output).take(BATCH_HEADER_LIMIT).read_until(b'\n', &mut header)
            .map_err(|_| "cannot read git cat-file reply")?;
        parse_batch_header(&header, oid.as_str().as_bytes()).ok_or_else(|| format!("Git object {oid} is missing or not a blob"))
    }

    /// Discard the next `count` content bytes without keeping them, then
    /// the reply's trailing LF.
    fn skip(&mut self, count: u64) -> Result<(), String> {
        let skipped = io::copy(&mut (&mut self.output).take(count), &mut io::sink()).map_err(|_| TRUNCATED_REPLY)?;
        if skipped != count {
            return Err(TRUNCATED_REPLY.into());
        }
        let mut end = [0u8; 1];
        self.output.read_exact(&mut end).map_err(|_| TRUNCATED_REPLY)?;
        if end != *b"\n" {
            return Err(MALFORMED_REPLY.into());
        }
        Ok(())
    }

    fn blob(&mut self, oid: &ObjectId, skip_large: bool) -> Result<Option<Vec<u8>>, String> {
        // The verified core checks the header and decides what to read.
        let size = self.request(oid)?;
        match blob_read(size, skip_large) {
            BlobRead::Read => {},
            BlobRead::TooLarge => return Err(too_large()),
            BlobRead::Skip => {
                self.skip(size)?;
                return Ok(None);
            },
        }
        // `blob_read` decided `Read`, so `size` is at most `MAX_RECORD`.
        let size = usize::try_from(size).map_err(|_| too_large())?;
        let mut data = vec![0u8; size + 1];
        self.output.read_exact(&mut data).map_err(|_| TRUNCATED_REPLY)?;
        if data.pop() != Some(b'\n') {
            return Err(MALFORMED_REPLY.into());
        }
        Ok(Some(data))
    }

    /// The size of blob `oid` and its first `ENVELOPE_PREFIX_LEN` bytes (all
    /// of a shorter blob): what the keyless envelope check needs. The rest is
    /// skipped unread, and so is a blob larger than any record (`None`).
    fn blob_prefix(&mut self, oid: &ObjectId) -> Result<Option<(usize, Vec<u8>)>, String> {
        let announced = self.request(oid)?;
        match blob_read(announced, true) {
            BlobRead::Read => {},
            BlobRead::TooLarge => return Err(too_large()),
            BlobRead::Skip => {
                self.skip(announced)?;
                return Ok(None);
            },
        }
        // `blob_read` decided `Read`, so the size is at most `MAX_RECORD`.
        let size = usize::try_from(announced).map_err(|_| too_large())?;
        let mut prefix = vec![0u8; size.min(ENVELOPE_PREFIX_LEN)];
        self.output.read_exact(&mut prefix).map_err(|_| TRUNCATED_REPLY)?;
        self.skip(announced - prefix.len() as u64)?;
        Ok(Some((size, prefix)))
    }
}

impl Drop for Objects {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
