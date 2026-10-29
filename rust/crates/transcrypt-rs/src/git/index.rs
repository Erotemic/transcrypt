//! Writing blobs and staging them: `IndexUpdate`.

use super::*;

/// The object id Git gives `bytes` (nothing is written).
pub(crate) fn blob_id(root: &Path, bytes: &[u8]) -> Result<String, String> {
    object_id(git_with_input(root, &["hash-object", "--no-filters", "--stdin"], bytes)?)
}

/// Write `bytes` as a Git blob, unfiltered; its verified object id.
pub(crate) fn hash_object(root: &Path, bytes: &[u8]) -> Result<String, String> {
    object_id(git_with_input(root, &["hash-object", "-w", "--no-filters", "--stdin"], bytes)?)
}

/// What an `IndexUpdate` stages, which decides how its blobs are written.
pub(crate) enum Blobs {
    /// v3 records (and the public config): streamed to Git as they are
    /// added, so memory holds one at a time. A failure part way may leave
    /// some unreferenced ciphertext in the object store, which is public.
    Records,
    /// Plaintext the user releases: held until `apply`, so that a failure
    /// before it leaves no plaintext object in the repository.
    Plaintext,
}

/// Blobs to stage at paths: written by one `git fast-import` (from stdin, so
/// no content touches a temporary file), then staged by one `update-index -z
/// --index-info`. One process each, however many files.
pub(crate) struct IndexUpdate {
    root: PathBuf,
    blobs: Blobs,
    importer: Option<Importer>,
    held: Vec<Zeroizing<Vec<u8>>>,
    entries: Vec<(String, Vec<u8>)>,
}

impl IndexUpdate {
    pub(crate) fn new(root: &Path, blobs: Blobs) -> IndexUpdate {
        IndexUpdate { root: root.to_path_buf(), blobs, importer: None, held: Vec::new(), entries: Vec::new() }
    }

    /// Stage `bytes` (unfiltered) as a blob of `mode` at `path`.
    pub(crate) fn add(&mut self, mode: &str, path: &[u8], bytes: &[u8]) -> Result<(), String> {
        self.entries.push((mode.to_owned(), path.to_owned()));
        match self.blobs {
            Blobs::Records => {
                let mark = self.entries.len();
                self.importer()?.blob(mark, bytes)
            },
            Blobs::Plaintext => {
                self.held.push(Zeroizing::new(bytes.to_vec()));
                Ok(())
            },
        }
    }

    pub(crate) fn len(&self) -> usize { self.entries.len() }

    fn importer(&mut self) -> Result<&mut Importer, String> {
        let (root, blobs) = (&self.root, &self.blobs);
        get_or_try_init(&mut self.importer, || Importer::spawn(root, blobs))
    }

    /// Write the blobs and stage them, with `update-index` `options` (such as
    /// `--add`). `update-index` skips a path it considers invalid (on
    /// Windows, one that NTFS cannot name) with only a warning and success,
    /// so the index is read back: every entry must now be staged exactly.
    pub(crate) fn apply(mut self, options: &[&str]) -> Result<(), String> {
        if self.entries.is_empty() { return Ok(()); }
        for (mark, bytes) in std::mem::take(&mut self.held).iter().enumerate() {
            self.importer()?.blob(mark + 1, bytes)?;
        }
        let marks = self.entries.len();
        let oids = self.importer()?.finish(marks)?;
        let root = &self.root;
        let mut info = Vec::new();
        for ((mode, path), oid) in self.entries.iter().zip(&oids) {
            push_index_record(&mut info, mode, oid, path);
        }
        let arguments: Vec<&str> = ["update-index", "-z"].into_iter().chain(options.iter().copied())
            .chain(["--index-info"]).collect();
        git_with_input(root, &arguments, &info)?;
        let listing = index_listing(root)?;
        let staged: std::collections::HashSet<&[u8]> = git_records(&listing)?.into_iter().collect();
        for ((mode, path), oid) in self.entries.iter().zip(oids) {
            let mut record = format!("{mode} {oid} 0\t").into_bytes();
            record.extend_from_slice(path);
            if !staged.contains(&record[..]) {
                return Err(format!("Git did not stage {} (it refuses that path name here)", String::from_utf8_lossy(path)));
            }
        }
        Ok(())
    }
}

/// Git settings for writing v3 records: their bytes are random, so no
/// compression shrinks them and no delta against another blob shortens
/// them, and trying costs most of the time of storing large files.
const RECORD_STORAGE: [&str; 6] = ["-c", "core.compression=0", "-c", "pack.compression=0", "-c", "core.loosecompression=0"];
/// `fast-import` tries deltas only for blobs below this size: none.
const NO_DELTAS: &str = "--big-file-threshold=1";

/// One `git fast-import`, fed each blob as it comes. Its output (the marks'
/// object ids) and errors are read by threads, so that neither pipe can
/// fill while blobs are still being written. `--done` makes it refuse a
/// stream that ends without `done` (but objects already written stay).
struct Importer {
    child: std::process::Child,
    input: Option<std::process::ChildStdin>,
    output: Option<std::thread::JoinHandle<io::Result<Vec<u8>>>>,
    errors: Option<std::thread::JoinHandle<Vec<u8>>>,
}

impl Importer {
    fn spawn(root: &Path, blobs: &Blobs) -> Result<Importer, String> {
        let mut command = git_command(Some(root));
        if matches!(blobs, Blobs::Records) { command.args(RECORD_STORAGE); }
        command.args(["fast-import", "--quiet", "--done"]);
        if matches!(blobs, Blobs::Records) { command.arg(NO_DELTAS); }
        let mut child = command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
            .spawn().map_err(|e| format!("cannot run git fast-import: {e}"))?;
        let input = child.stdin.take().ok_or("git fast-import input pipe missing")?;
        let output = child.stdout.take().ok_or("git fast-import output pipe missing")?;
        let errors = child.stderr.take().ok_or("git fast-import error pipe missing")?;
        let output = std::thread::spawn(move || {
            let mut marks = Vec::new();
            output.take(GIT_OUTPUT_LIMIT as u64).read_to_end(&mut marks).map(|_| marks)
        });
        let errors = std::thread::spawn(move || {
            let mut errors = errors;
            let mut kept = Vec::new();
            let _ = (&mut errors).take(KEPT_ERROR_OUTPUT as u64).read_to_end(&mut kept);
            let _ = io::copy(&mut errors, &mut io::sink());
            kept
        });
        Ok(Importer { child, input: Some(input), output: Some(output), errors: Some(errors) })
    }

    fn write(&mut self, bytes: &[u8]) -> Result<(), String> {
        let input = self.input.as_mut().ok_or("git fast-import input closed")?;
        sigpipe_blocked(input, |input| input.write_all(bytes)).map_err(|_| self.failure())
    }

    /// Write `bytes` as the blob of `mark`.
    fn blob(&mut self, mark: usize, bytes: &[u8]) -> Result<(), String> {
        self.write(format!("blob\nmark :{mark}\ndata {}\n", bytes.len()).as_bytes())?;
        self.write(bytes)?;
        self.write(b"\n")
    }

    /// Ask for the object ids of marks 1 to `marks`, end the stream, and
    /// wait: each id, in order.
    fn finish(&mut self, marks: usize) -> Result<Vec<String>, String> {
        let mut requests: String = (1..=marks).map(|mark| format!("get-mark :{mark}\n")).collect();
        requests.push_str("done\n");
        self.write(requests.as_bytes())?;
        drop(self.input.take());
        let output = self.output.take().and_then(|o| o.join().ok()).and_then(Result::ok);
        let status = self.child.wait().map_err(|_| "cannot wait for git fast-import")?;
        let Some(output) = output.filter(|_| status.success()) else { return Err(self.failure()) };
        let oids: Vec<String> = output.split(|b| *b == b'\n').filter(|l| !l.is_empty())
            .map(|l| String::from_utf8_lossy(l).into_owned()).collect();
        if oids.len() != marks || !oids.iter().all(|oid| is_object_id(oid.as_bytes())) {
            return Err("malformed git fast-import output".into());
        }
        Ok(oids)
    }

    /// Stop the import, with what it said on its way out.
    fn failure(&mut self) -> String {
        drop(self.input.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
        let errors = self.errors.take().and_then(|e| e.join().ok()).unwrap_or_default();
        format!("git fast-import failed: {}", String::from_utf8_lossy(&errors).trim())
    }
}

impl Drop for Importer {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Append the `update-index -z --index-info` record `<mode> SP <oid> TAB
/// <path> NUL` to `info`.
pub(crate) fn push_index_record(info: &mut Vec<u8>, mode: &str, oid: &str, path: &[u8]) {
    info.extend_from_slice(format!("{mode} {oid}\t").as_bytes());
    info.extend_from_slice(path);
    info.push(0);
}

fn object_id(output: Vec<u8>) -> Result<String, String> {
    let oid = String::from_utf8_lossy(&output).trim_end().to_owned();
    if !is_object_id(oid.as_bytes()) { return Err("malformed git hash-object output".into()); }
    Ok(oid)
}
