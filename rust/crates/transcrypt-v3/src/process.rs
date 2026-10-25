//! Git's long-running filter protocol (`filter.transcrypt-v3.process`,
//! version 2): one process serves every clean and smudge of a Git command,
//! instead of one process per file. Packet lengths are decoded by the
//! verified core (`decode_pkt_len`), and every file goes through the same
//! `convert` as the per-file filters. Any malformed exchange ends the
//! process, which makes Git fail the command (the filter is required).

use std::{
    io::{self, Read, Write},
    path::Path,
};
use transcrypt_v3_core::{decode_pkt_len, MAX_PKT_LEN, MAX_RECORD};
use zeroize::Zeroizing;
use crate::convert;

/// The most data one packet carries.
const MAX_DATA: usize = MAX_PKT_LEN - 4;

/// One packet, or `None` for a flush packet.
fn read_packet(input: &mut impl Read) -> Result<Option<Zeroizing<Vec<u8>>>, String> {
    let mut header = [0u8; 4];
    input.read_exact(&mut header).map_err(|_| "Git closed the filter stream")?;
    let len = decode_pkt_len(&header).map_err(|_| "malformed pkt-line from Git")?;
    if len == 0 { return Ok(None); }
    let mut data = Zeroizing::new(vec![0u8; len - 4]);
    input.read_exact(&mut data).map_err(|_| "truncated pkt-line from Git")?;
    Ok(Some(data))
}

/// Text packets (each without its trailing LF) up to the next flush.
fn read_list(input: &mut impl Read) -> Result<Vec<Vec<u8>>, String> {
    let mut list = Vec::new();
    while let Some(mut line) = read_packet(input)? {
        if line.last() == Some(&b'\n') { line.pop(); }
        list.push(line.to_vec());
    }
    Ok(list)
}

/// Like `read_list`, but `None` if Git ended the session cleanly instead.
fn read_request(input: &mut impl Read) -> Result<Option<Vec<Vec<u8>>>, String> {
    let mut first = [0u8; 1];
    match input.read(&mut first) {
        Ok(0) => return Ok(None),
        Ok(_) => {},
        Err(_) => return Err("cannot read from Git".into()),
    }
    read_list(&mut first.chain(input)).map(Some)
}

fn write_packet(out: &mut impl Write, data: &[u8]) -> io::Result<()> {
    write!(out, "{:04x}", data.len() + 4)?;
    out.write_all(data)
}

fn write_text(out: &mut impl Write, text: &str) -> io::Result<()> {
    write_packet(out, format!("{text}\n").as_bytes())
}

fn write_flush(out: &mut impl Write) -> io::Result<()> {
    out.write_all(b"0000")
}

/// Append without leaving an unwiped copy behind when the buffer grows.
fn append(buffer: &mut Zeroizing<Vec<u8>>, data: &[u8]) {
    if buffer.len() + data.len() > buffer.capacity() {
        let mut bigger = Zeroizing::new(Vec::with_capacity((buffer.len() + data.len()).max(2 * buffer.capacity())));
        bigger.extend_from_slice(buffer);
        *buffer = bigger;
    }
    buffer.extend_from_slice(data);
}

pub(crate) fn serve(root: &Path) -> Result<(), String> {
    let mut input = io::stdin().lock();
    let mut output = io::BufWriter::new(io::stdout().lock());
    let io_error = |_| "cannot write to Git".to_owned();
    // Handshake: Git announces itself and its versions, then capabilities.
    let hello = read_list(&mut input)?;
    if hello.first().map(Vec::as_slice) != Some(b"git-filter-client") || !hello.iter().any(|l| l == b"version=2") {
        return Err("unsupported Git filter protocol".into());
    }
    write_text(&mut output, "git-filter-server").map_err(io_error)?;
    write_text(&mut output, "version=2").map_err(io_error)?;
    write_flush(&mut output).map_err(io_error)?;
    output.flush().map_err(io_error)?;
    let capabilities = read_list(&mut input)?;
    for capability in ["capability=clean", "capability=smudge"] {
        if capabilities.iter().any(|c| c == capability.as_bytes()) {
            write_text(&mut output, capability).map_err(io_error)?;
        }
    }
    write_flush(&mut output).map_err(io_error)?;
    output.flush().map_err(io_error)?;
    while let Some(request) = read_request(&mut input)? {
        let value = |key: &[u8]| request.iter().find_map(|line| line.strip_prefix(key)).map(<[u8]>::to_vec);
        let (command, path) = (value(b"command="), value(b"pathname="));
        // The content, refused (but still read to the flush) beyond the bound.
        let mut content = Zeroizing::new(Vec::new());
        let mut too_large = false;
        while let Some(data) = read_packet(&mut input)? {
            too_large |= content.len() + data.len() > MAX_RECORD;
            if !too_large { append(&mut content, &data); }
        }
        let result = match (command.as_deref(), &path) {
            _ if too_large => Err("input exceeds the 16 MiB v3 size limit".into()),
            (Some(b"clean"), Some(path)) => convert(root, true, path, content),
            (Some(b"smudge"), Some(path)) => convert(root, false, path, content),
            _ => Err("unsupported filter request".to_owned()),
        };
        match result {
            Ok(converted) => {
                write_text(&mut output, "status=success").map_err(io_error)?;
                write_flush(&mut output).map_err(io_error)?;
                for chunk in converted.chunks(MAX_DATA) {
                    write_packet(&mut output, chunk).map_err(io_error)?;
                }
                write_flush(&mut output).map_err(io_error)?;
                // An empty list keeps the status.
                write_flush(&mut output).map_err(io_error)?;
            },
            Err(e) => {
                eprintln!("transcrypt-v3: {}: {e}", String::from_utf8_lossy(path.as_deref().unwrap_or_default()));
                write_text(&mut output, "status=error").map_err(io_error)?;
                write_flush(&mut output).map_err(io_error)?;
            },
        }
        output.flush().map_err(io_error)?;
    }
    Ok(())
}
