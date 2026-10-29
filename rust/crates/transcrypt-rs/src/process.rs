//! Git's long-running filter protocol (`filter.transcrypt-v3.process`,
//! version 2): one process serves every clean and smudge of a Git command,
//! instead of one process per file. Packet lengths are decoded by the
//! verified core (`decode_pkt_len`), and every file goes through the same
//! `Filters::convert` as the per-file filters (which reloads the key only
//! when the config changes). Any malformed exchange ends the process, which
//! makes Git fail the command (the filter is required).

use std::{
    io::{self, Read, Write},
    path::Path,
};
use transcrypt_v3_core::{decode_pkt_len, MAX_PKT_LEN, MAX_RECORD, PKT_HEADER_LEN};
use zeroize::Zeroizing;
use crate::{filter::Filters, git::{append_wiped, TOO_LARGE}};

/// The flush packet: a header of length 0.
const FLUSH_PKT: &[u8; PKT_HEADER_LEN] = b"0000";
/// The most data one packet carries.
const MAX_DATA: usize = MAX_PKT_LEN - PKT_HEADER_LEN;

/// One packet, or `None` for a flush packet.
fn read_packet(input: &mut impl Read) -> Result<Option<Zeroizing<Vec<u8>>>, String> {
    let mut header = [0u8; PKT_HEADER_LEN];
    input.read_exact(&mut header).map_err(|_| "Git closed the filter stream")?;
    let len = decode_pkt_len(&header).map_err(|_| "malformed pkt-line from Git")?;
    if len == 0 { return Ok(None); }
    let mut data = Zeroizing::new(vec![0u8; len - PKT_HEADER_LEN]);
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
    write!(out, "{:0PKT_HEADER_LEN$x}", data.len() + PKT_HEADER_LEN)?;
    out.write_all(data)
}

fn write_text(out: &mut impl Write, text: &str) -> io::Result<()> {
    write_packet(out, format!("{text}\n").as_bytes())
}

fn write_flush(out: &mut impl Write) -> io::Result<()> {
    out.write_all(FLUSH_PKT)
}

/// A flush packet, and everything written before it sent to Git at once.
fn send_flush(out: &mut impl Write) -> io::Result<()> {
    write_flush(out)?;
    out.flush()
}

/// Text packets, then a flush, sent to Git at once.
fn write_list(out: &mut impl Write, lines: &[&str]) -> io::Result<()> {
    for line in lines { write_text(out, line)?; }
    send_flush(out)
}

/// The reply to one request: the converted content, or an error status.
fn write_reply(out: &mut impl Write, converted: Option<&[u8]>) -> io::Result<()> {
    let Some(data) = converted else { return write_list(out, &["status=error"]) };
    write_text(out, "status=success")?;
    write_flush(out)?;
    for chunk in data.chunks(MAX_DATA) { write_packet(out, chunk)?; }
    write_flush(out)?;
    // An empty status list keeps the status.
    send_flush(out)
}

pub(crate) fn serve(root: &Path) -> Result<(), String> {
    let mut input = io::stdin().lock();
    let mut output = io::BufWriter::new(io::stdout().lock());
    let io_error = |_: io::Error| "cannot write to Git".to_owned();
    // Handshake: Git announces itself and its versions, then capabilities.
    let hello = read_list(&mut input)?;
    if hello.first().map(Vec::as_slice) != Some(b"git-filter-client") || !hello.iter().any(|l| l == b"version=2") {
        return Err("unsupported Git filter protocol".into());
    }
    write_list(&mut output, &["git-filter-server", "version=2"]).map_err(io_error)?;
    let capabilities = read_list(&mut input)?;
    let offered: Vec<&str> = ["capability=clean", "capability=smudge"].into_iter()
        .filter(|wanted| capabilities.iter().any(|c| c == wanted.as_bytes())).collect();
    write_list(&mut output, &offered).map_err(io_error)?;
    let mut filters = Filters::new(root);
    while let Some(request) = read_request(&mut input)? {
        let value = |key: &[u8]| request.iter().find_map(|line| line.strip_prefix(key));
        let (command, path) = (value(b"command="), value(b"pathname="));
        // The content, refused (but still read to the flush) beyond the bound.
        let mut content = Zeroizing::new(Vec::new());
        let mut too_large = false;
        while let Some(data) = read_packet(&mut input)? {
            too_large |= content.len() + data.len() > MAX_RECORD;
            if !too_large { append_wiped(&mut content, &data); }
        }
        let result = match (command, path) {
            _ if too_large => Err(TOO_LARGE.into()),
            (Some(b"clean"), Some(path)) => filters.convert(true, path, content),
            (Some(b"smudge"), Some(path)) => filters.convert(false, path, content),
            _ => Err("unsupported filter request".to_owned()),
        };
        if let Err(e) = &result {
            eprintln!("transcrypt-rs: {}: {e}", String::from_utf8_lossy(path.unwrap_or_default()));
        }
        write_reply(&mut output, result.as_ref().ok().map(|c| c.as_slice())).map_err(io_error)?;
    }
    Ok(())
}
