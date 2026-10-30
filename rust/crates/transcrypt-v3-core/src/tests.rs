//! Unit tests of the core (`#[cfg(test)]`, not extracted to Lean).

use super::*;

#[test]
fn literal_lengths_are_the_field_sums() {
    assert_eq!(CONFIG_PREFIX_LEN, CONFIG_MAGIC.len() + SALT_LEN);
    assert_eq!(CONFIG_LEN, CONFIG_PREFIX_LEN + TAG_LEN);
    assert_eq!(FILE_HEADER_LEN, FILE_MAGIC.len() + ID_LEN);
    assert_eq!(FRAME_CONFIG_START, size_of::<u8>());
    assert_eq!(FRAME_LEN_START, FRAME_CONFIG_START + CONFIG_LEN);
    assert_eq!(BE_U32_LEN, size_of::<u32>());
    assert_eq!(BLOB_FIELD_LEN, BLOB_FIELD.len());
    assert_eq!(MAX_SIZE_DIGITS, u64::MAX.ilog10() as usize);
}

#[test]
fn config_codec_roundtrip_strict_length_and_magic() {
    let salt = core::array::from_fn(|i| i as u8);
    let tag = core::array::from_fn(|i| (255 - i) as u8);
    let config = Config { salt, tag };
    let bytes = encode_config(&config);
    assert_eq!(decode_config_exact(&bytes), Ok(config));
    assert_eq!(parse_config(&bytes), Ok(config));
    for n in 0..CONFIG_LEN {
        assert_eq!(parse_config(&bytes[..n]), Err(FormatError::Length));
    }
    let mut extended = bytes.to_vec();
    extended.push(1);
    assert_eq!(parse_config(&extended), Err(FormatError::Length));
    // Each byte of the version marker must be enforced, with no
    // exceptions for offsets 5 or 6 and no fallback to older formats.
    for pos in 0..CONFIG_MAGIC.len() {
        let mut modified = bytes;
        modified[pos] ^= 1;
        assert_eq!(decode_config_exact(&modified), Err(FormatError::Magic));
        assert_eq!(parse_config(&modified), Err(FormatError::Magic));
    }
}

#[test]
fn file_header_codec_roundtrip_strict_length_and_magic() {
    let id = core::array::from_fn(|i| (i * 11) as u8);
    let header = encode_file_header(&id);
    assert_eq!(decode_file_header_exact(&header), Ok(id));
    for n in [FILE_MIN_LEN, FILE_MIN_LEN + 1, FILE_MIN_LEN + 255] {
        let mut blob = header.to_vec();
        blob.resize(n, 0x7f);
        assert_eq!(parse_file_header(&blob), Ok(id));
    }
    let mut record = header.to_vec();
    record.extend_from_slice(&[0x66; TAG_LEN]);
    for n in 0..FILE_MIN_LEN {
        assert_eq!(parse_file_header(&record[..n]), Err(FormatError::Length));
    }
    for pos in 0..FILE_MAGIC.len() {
        let mut modified = header;
        modified[pos] ^= 1;
        assert_eq!(decode_file_header_exact(&modified), Err(FormatError::Magic));
        let mut blob = modified.to_vec();
        blob.extend_from_slice(&[0u8; TAG_LEN]);
        assert_eq!(parse_file_header(&blob), Err(FormatError::Magic));
    }
}

/// A deterministic toy primitive: NOT cryptography. It exists only so the
/// decision core can be exercised without the adapter's RustCrypto stack.
/// The "tag" mixes key, config, path and plaintext so that changing any
/// one of them makes `open_file` fail, mirroring the AES-SIV contract.
struct Mock {
    key: u8,
}

impl Mock {
    fn mac(&self, parts: &[&[u8]]) -> [u8; TAG_LEN] {
        let mut tag = [self.key; TAG_LEN];
        let mut n = 0usize;
        for part in parts {
            for &b in part.iter() {
                tag[n % TAG_LEN] = tag[n % TAG_LEN].rotate_left(3) ^ b ^ (n as u8);
                n += 1;
            }
            tag[n % TAG_LEN] ^= 0xa5;
            n += 1;
        }
        tag
    }
}

impl V3Primitives for Mock {
    fn seal_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &mut [u8; TAG_LEN]) -> bool {
        *tag = self.mac(&[b"config", prefix]);
        true
    }
    fn open_config(&self, prefix: &[u8; CONFIG_PREFIX_LEN], tag: &[u8; TAG_LEN]) -> bool {
        self.mac(&[b"config", prefix]) == *tag
    }
    fn seal_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], plaintext: &[u8], out: &mut [u8]) -> bool {
        if out.len() != plaintext.len() + TAG_LEN {
            return false;
        }
        out[..TAG_LEN].copy_from_slice(&self.mac(&[b"file", config, path, plaintext]));
        for (o, p) in out[TAG_LEN..].iter_mut().zip(plaintext) {
            *o = p ^ self.key;
        }
        true
    }
    fn open_file(&self, config: &[u8; CONFIG_LEN], path: &[u8], sealed: &[u8], out: &mut [u8]) -> bool {
        if sealed.len() < TAG_LEN || out.len() != sealed.len() - TAG_LEN {
            return false;
        }
        let plaintext: std::vec::Vec<u8> = sealed[TAG_LEN..].iter().map(|c| c ^ self.key).collect();
        if self.mac(&[b"file", config, path, &plaintext]) != sealed[..TAG_LEN] {
            return false;
        }
        out.copy_from_slice(&plaintext);
        true
    }
    fn config_id(&self, config: &[u8; CONFIG_LEN]) -> [u8; ID_LEN] {
        self.mac(&[b"id", config])
    }
}

fn seal(m: &Mock, config: &[u8; CONFIG_LEN], path: &[u8], pt: &[u8]) -> Result<std::vec::Vec<u8>, Refusal> {
    let mut out = std::vec![0u8; pt.len() + FILE_MIN_LEN];
    seal_record(m, config, path, pt, &mut out).map(|_| out)
}

fn open(m: &Mock, config: &[u8; CONFIG_LEN], path: &[u8], record: &[u8]) -> Result<std::vec::Vec<u8>, Refusal> {
    let mut out = std::vec![0u8; record.len().saturating_sub(FILE_MIN_LEN)];
    open_record(m, config, path, record, &mut out).map(|_| out)
}

#[test]
fn canonical_path_policy() {
    for good in [b"a.secret".as_slice(), b"dir/x.secret", b"a b.secret", b".secret", b"d/.secret",
                 b"raw/\xff.secret", b"dir/new\nline.secret", b"...secret", b"a/.../b.secret",
                 b".env", b"config/production.yaml", b"private/key", b"x", b"x.secret.txt",
                 b"d/.transcrypt/config", b".transcrypt", b"a.gitattributes", b"d/.gitmodules",
                 b".gitattributes.d/x"] {
        assert!(is_canonical_protected_path(good), "rejected {:?}", good);
    }
    for bad in [b"".as_slice(), b"/root.secret", b"../bad.secret", b"x/../bad.secret",
                b"./x.secret", b"x//y.secret", b"x/./y.secret", b"x.secret/", b"evil\0.secret",
                b"x.secret/..", b"x.secret/.", b".transcrypt/config", b".transcrypt/x",
                b".gitattributes", b"d/.gitattributes", b".gitmodules"] {
        assert!(!is_canonical_protected_path(bad), "accepted {:?}", bad);
    }
    let mut long = std::vec![b'x'; MAX_PATH];
    assert!(is_canonical_protected_path(&long));
    long.push(b'x');
    assert!(!is_canonical_protected_path(&long));
    assert!(is_reserved_path(b".transcrypt/") && !is_reserved_path(b".transcrypt"));
}

#[test]
fn sealed_records_are_bound_to_config_and_path() {
    let m = Mock { key: 9 };
    let config = initialize_config(&m, &[3u8; SALT_LEN]).unwrap();
    assert!(authenticate_config(&m, &config).is_ok());
    assert_eq!(authenticate_config(&Mock { key: 10 }, &config), Err(Refusal::ConfigAuthentication));
    let mut bad = config;
    bad[0] ^= 1;
    assert_eq!(authenticate_config(&m, &bad), Err(Refusal::Config));
    for pt in [b"".as_slice(), b"hello", &[0u8, 1, 255]] {
        let rec = seal(&m, &config, b"v/a.secret", pt).unwrap();
        assert_eq!(&rec[..FILE_HEADER_LEN], &encode_file_header(&m.config_id(&config)));
        assert_eq!(open(&m, &config, b"v/a.secret", &rec).unwrap(), pt);
        assert_eq!(open(&m, &config, b"v/b.secret", &rec), Err(Refusal::Authentication));
        let mut flipped = rec.clone();
        *flipped.last_mut().unwrap() ^= 1;
        assert!(open(&m, &config, b"v/a.secret", &flipped).is_err());
        assert_eq!(seal(&m, &config, b"v/a.secret", &rec), Err(Refusal::DoubleEncryption));
        assert_eq!(seal(&m, &config, b"../a.secret", pt), Err(Refusal::Path));
        assert_eq!(open(&m, &config, b".gitattributes", &rec), Err(Refusal::Path));
    }
    let other = initialize_config(&m, &[4u8; SALT_LEN]).unwrap();
    let rec = seal(&m, &config, b"a.secret", b"x").unwrap();
    assert_eq!(open(&m, &other, b"a.secret", &rec), Err(Refusal::ConfigMismatch));
    assert_eq!(open(&m, &config, b"a.secret", &rec[..FILE_MIN_LEN - 1]), Err(Refusal::Envelope));
    let mut out = [0u8; 2];
    assert_eq!(open_record(&m, &config, b"a.secret", &rec, &mut out), Err(Refusal::Size));
    assert_eq!(seal_record(&m, &config, b"a.secret", b"x", &mut out), Err(Refusal::Size));
}

#[test]
fn lifecycle_actions_never_discard_unknown_bytes() {
    let m = Mock { key: 1 };
    let config = initialize_config(&m, &[5u8; SALT_LEN]).unwrap();
    let rec = seal(&m, &config, b"a.secret", b"plain").unwrap();
    assert_eq!(hydrate_action(&rec, &rec, b"plain"), Ok(HydrateAction::Publish));
    assert_eq!(hydrate_action(b"plain", &rec, b"plain"), Ok(HydrateAction::Keep));
    assert_eq!(hydrate_action(b"edited", &rec, b"plain"), Err(Refusal::UnexpectedWorktree));
    assert_eq!(lock_action(&rec, &rec, b""), Ok(LockAction::Keep));
    let resealed = seal(&m, &config, b"a.secret", b"plain").unwrap();
    assert_eq!(lock_action(b"plain", &rec, &resealed), Ok(LockAction::Flush));
    let resealed = seal(&m, &config, b"a.secret", b"edited").unwrap();
    assert_eq!(lock_action(b"edited", &rec, &resealed), Err(Refusal::UnexpectedWorktree));
}

#[test]
fn agent_requests_are_authorized_against_the_active_config() {
    let a = [1u8; CONFIG_LEN];
    let mut b = a;
    b[54] = 2;
    assert_eq!(authorize_agent_request(b'P', &a, &a, b"", 0), Ok(AgentOp::Ping));
    assert_eq!(authorize_agent_request(b'X', &a, &a, b"", 0), Ok(AgentOp::Stop));
    assert_eq!(authorize_agent_request(b'E', &a, &a, b"x.secret", 9), Ok(AgentOp::Encrypt));
    assert_eq!(authorize_agent_request(b'D', &a, &a, b"x.secret", 0), Ok(AgentOp::Decrypt));
    assert_eq!(authorize_agent_request(b'D', &b, &a, b"x.secret", 0), Err(Refusal::ConfigMismatch));
    assert_eq!(authorize_agent_request(b'E', &a, &a, b".transcrypt/config", 0), Err(Refusal::Path));
    assert_eq!(authorize_agent_request(b'P', &a, &a, b"x.secret", 0), Err(Refusal::Request));
    assert_eq!(authorize_agent_request(b'X', &a, &a, b"", 1), Err(Refusal::Request));
    assert_eq!(authorize_agent_request(b'Q', &a, &a, b"", 0), Err(Refusal::Request));
    assert_eq!(authorize_agent_request(b'E', &a, &a, b"x.secret", MAX_RECORD + 1), Err(Refusal::Size));
}

#[test]
fn attr_records_name_the_requested_path_and_its_filter() {
    let response = b"a.secret\0filter\0transcrypt-v3\0d/b c\0filter\0unspecified\0e\0filter\0transcrypt-v3x\0";
    let first = parse_attr_record(response, 0, b"a.secret").unwrap();
    assert!(first.protected);
    let second = parse_attr_record(response, first.next, b"d/b c").unwrap();
    assert!(!second.protected);
    let third = parse_attr_record(response, second.next, b"e").unwrap();
    assert!(!third.protected);
    assert_eq!(third.next, response.len());
    assert_eq!(parse_attr_record(response, third.next, b""), Err(Refusal::Attribute));
    // Another path, another attribute, a truncated record, a start beyond the end.
    assert_eq!(parse_attr_record(response, 0, b"a.secreT"), Err(Refusal::Attribute));
    assert_eq!(parse_attr_record(response, 0, b"a"), Err(Refusal::Attribute));
    assert_eq!(parse_attr_record(b"a\0diff\0transcrypt-v3\0", 0, b"a"), Err(Refusal::Attribute));
    assert_eq!(parse_attr_record(b"a\0filter\0transcrypt-v3", 0, b"a"), Err(Refusal::Attribute));
    assert_eq!(parse_attr_record(response, response.len() + 1, b""), Err(Refusal::Attribute));
    // A path containing what looks like a record separator still must match exactly.
    let tricky = b"x\0filter\0transcrypt-v3\0";
    assert!(parse_attr_record(tricky, 0, b"x").unwrap().protected);
    assert_eq!(parse_attr_record(tricky, 0, b"x\0filter"), Err(Refusal::Attribute));
}

#[test]
fn attr_responses_must_answer_every_path_in_order() {
    let request = b"a.secret\0d/b c\0e\0";
    let response = b"a.secret\0filter\0transcrypt-v3\0d/b c\0filter\0unspecified\0e\0filter\0transcrypt-v3\0";
    let mut flags = [false; 3];
    assert!(parse_attr_response(request, response, &mut flags));
    assert_eq!(flags, [true, false, true]);
    assert!(parse_attr_response(b"", b"", &mut []));
    assert!(!parse_attr_response(b"", b"x", &mut []));
    // Truncated, extended, reordered, too few or too many slots, unterminated request.
    assert!(!parse_attr_response(request, &response[..response.len() - 1], &mut flags));
    assert!(!parse_attr_response(request, &[&response[..], b"x"].concat(), &mut flags));
    assert!(!parse_attr_response(b"e\0a.secret\0d/b c\0", response, &mut flags));
    assert!(!parse_attr_response(request, response, &mut [false; 2]));
    assert!(!parse_attr_response(request, response, &mut [false; 4]));
    assert!(!parse_attr_response(b"a.secret\0d/b c\0e", response, &mut flags));
}

#[test]
fn smudge_keeps_only_records_and_opens_only_its_own_config() {
    let id = [7u8; ID_LEN];
    let mut record = std::vec::Vec::from(&encode_file_header(&id)[..]);
    record.extend_from_slice(&[0u8; TAG_LEN]);
    assert_eq!(smudge_action(&record, &id, true), Ok(SmudgeAction::Open));
    assert_eq!(smudge_action(&record, &id, false), Ok(SmudgeAction::Keep));
    assert_eq!(smudge_action(&record, &[8u8; ID_LEN], true), Ok(SmudgeAction::Keep));
    assert_eq!(smudge_action(b"plaintext that bypassed the filter", &id, true), Err(Refusal::Foreign));
    assert_eq!(smudge_action(b"", &id, false), Err(Refusal::Foreign));
    assert_eq!(smudge_action(&std::vec![0u8; MAX_RECORD + 1], &id, true), Err(Refusal::Size));
}

#[test]
fn index_entries_are_parsed_at_the_first_tab_and_stage_zero_only() {
    let oid = b"0123456789abcdef0123456789abcdef01234567";
    let mut e = std::vec::Vec::new();
    e.extend_from_slice(b"100644 ");
    e.extend_from_slice(oid);
    e.extend_from_slice(b" 0\tdir/a\tb.secret");
    let parsed = parse_index_entry(&e).unwrap();
    assert!(parsed.regular);
    assert_eq!(&e[parsed.path_start..], b"dir/a\tb.secret");
    let exec: std::vec::Vec<u8> = [b"100755 ".as_slice(), oid, b" 0\tx.secret"].concat();
    assert!(parse_index_entry(&exec).unwrap().regular);
    let group: std::vec::Vec<u8> = [b"100664 ".as_slice(), oid, b" 0\tx.secret"].concat();
    assert!(!parse_index_entry(&group).unwrap().regular);
    let link: std::vec::Vec<u8> = [b"120000 ".as_slice(), oid, b" 0\tx.secret"].concat();
    assert!(!parse_index_entry(&link).unwrap().regular);
    for bad in [
        [b"100644 ".as_slice(), oid, b" 1\tx.secret"].concat(),  // unmerged
        [b"100644 ".as_slice(), oid, b" 0\t"].concat(),          // empty path
        [b"100644 ".as_slice(), oid, b" 0 x.secret"].concat(),    // no tab
        b"100644 0\tx".to_vec(),                                  // missing object id
        [b"1006440".as_slice(), oid, b" 0\tx.secret"].concat(),  // no separator
        std::vec::Vec::new(),
    ] {
        assert_eq!(parse_index_entry(&bad), Err(Refusal::Index), "{bad:?}");
    }
}

#[test]
fn object_ids_and_record_envelopes() {
    assert!(is_object_id(&[b'0'; 40]));
    assert!(is_object_id(&[b'f'; 64]));
    for bad in [&b""[..], &[b'0'; 39], &[b'0'; 41], &[b'0'; 63], &[b'A'; 40], &[b'g'; 40], b"-0000000000000000000000000000000000000000"] {
        assert!(!is_object_id(bad), "{bad:?}");
    }
    let mut colon = [b'0'; 40];
    colon[1] = b':';
    assert!(!is_object_id(&colon));
    let id = core::array::from_fn(|i| i as u8);
    let header = encode_file_header(&id);
    let mut record = std::vec::Vec::from(&header[..]);
    record.extend_from_slice(&[0u8; TAG_LEN]);
    assert!(record_envelope_ok(&record, &id));
    assert!(!record_envelope_ok(&record[..FILE_MIN_LEN - 1], &id));
    let mut other = id;
    other[0] ^= 1;
    assert!(!record_envelope_ok(&record, &other));
    record[0] ^= 1;
    assert!(!record_envelope_ok(&record, &id));
    assert!(!record_envelope_ok(b"plaintext that is long enough to pass the size bound", &id));
}

#[test]
fn envelope_prefix_refuses_impossible_sizes() {
    let id = core::array::from_fn(|i| i as u8);
    let header = encode_file_header(&id);
    let mut prefix = std::vec::Vec::from(&header[..]);
    prefix.extend_from_slice(&[0u8; TAG_LEN]);
    assert_eq!(prefix.len(), ENVELOPE_PREFIX_LEN);
    assert!(record_envelope_prefix_ok(FILE_MIN_LEN, &prefix, &id));
    assert!(record_envelope_prefix_ok(MAX_RECORD, &prefix, &id));
    // A declared size too small to hold a record, whatever the prefix.
    for size in [0, 1, FILE_HEADER_LEN, FILE_MIN_LEN - 1] {
        assert!(!record_envelope_prefix_ok(size, &prefix, &id), "{size}");
    }
    assert!(!record_envelope_prefix_ok(MAX_RECORD + 1, &prefix, &id));
    assert!(!record_envelope_prefix_ok(usize::MAX, &prefix, &id));
    // A prefix longer than the declared size.
    let mut longer = prefix.clone();
    longer.push(0);
    assert!(record_envelope_prefix_ok(FILE_MIN_LEN + 1, &longer, &id));
    assert!(!record_envelope_prefix_ok(FILE_MIN_LEN, &longer, &id));
    // A prefix shorter than `ENVELOPE_PREFIX_LEN` cannot show the envelope.
    assert!(!record_envelope_prefix_ok(FILE_MIN_LEN, &prefix[..FILE_MIN_LEN - 1], &id));
}

#[test]
fn envelope_prefix_decides_as_the_whole_record() {
    let id = core::array::from_fn(|i| i as u8);
    let mut other = id;
    other[0] ^= 1;
    let header = encode_file_header(&id);
    let mut bad_magic = header;
    bad_magic[0] ^= 1;
    let sizes = [0, FILE_HEADER_LEN, FILE_MIN_LEN - 1, FILE_MIN_LEN, FILE_MIN_LEN + 1, MAX_RECORD, MAX_RECORD + 1];
    for start in [&header[..], &bad_magic[..], b"plaintext"] {
        for size in sizes {
            let mut record = std::vec::Vec::from(&start[..start.len().min(size)]);
            record.resize(size, 0);
            let prefix = &record[..size.min(ENVELOPE_PREFIX_LEN)];
            for want in [&id, &other] {
                let whole = record_envelope_ok(&record, want);
                assert_eq!(record_envelope_prefix_ok(size, prefix, want), whole, "{size} {start:?}");
                assert_eq!(whole, start == &header[..] && want == &id && (FILE_MIN_LEN..=MAX_RECORD).contains(&size));
            }
        }
    }
}

#[test]
fn only_local_changes_are_repaired() {
    use SealAction::*;
    for (opens, local, envelope, moved, expected) in [
        (true, true, true, true, Keep), (true, false, false, false, Keep),
        (false, false, false, false, Leave), (false, false, true, true, Leave),
        (false, true, false, false, Seal), (false, true, false, true, Seal),
        (false, true, true, true, Rebind), (false, true, true, false, Leave),
    ] {
        assert_eq!(seal_action(opens, local, envelope, moved), expected);
    }
}

#[test]
fn keyless_or_settled_entries_check_the_envelope() {
    use EntryCheck::*;
    for (keyed, incremental, settled, expected) in [
        (true, false, false, Authenticate), (true, false, true, Authenticate),
        (true, true, false, Authenticate), (true, true, true, Envelope),
        (false, false, false, EnvelopeNotMoved), (false, false, true, Envelope),
        (false, true, false, EnvelopeNotMoved), (false, true, true, Envelope),
    ] {
        assert_eq!(entry_check(keyed, incremental, settled), expected);
    }
}

#[test]
fn object_ids_start_after_the_mode() {
    assert_eq!(OID_START, REGULAR_MODE.len() + 1);
    assert_eq!(OID_START, EXECUTABLE_MODE.len() + 1);
    assert_eq!(OID_START, MODE_LEN + 1);
    assert_eq!(OID_END_LEN, OID_END.len());
    assert_eq!(ENTRY_FIXED_LEN, OID_START + OID_END_LEN);
}

#[test]
fn pkt_line_lengths() {
    assert_eq!(decode_pkt_len(b"0000"), Ok(0));
    assert_eq!(decode_pkt_len(b"0005"), Ok(5));
    assert_eq!(decode_pkt_len(b"00ff"), Ok(255));
    assert_eq!(decode_pkt_len(b"fff0"), Ok(MAX_PKT_LEN));
    for bad in [b"0001", b"0004", b"fff1", b"ffff", b"00FF", b"00g0", b" 005", b"-005"] {
        assert_eq!(decode_pkt_len(bad), Err(Refusal::Request), "{bad:?}");
    }
}

#[test]
fn agent_frames_roundtrip() {
    let config = core::array::from_fn(|i| (i * 7) as u8);
    for len in [0u32, 1, 255, 256, 4096, 0x0102_0304, u32::MAX] {
        let h = encode_frame_header(b'D', &config, len);
        assert_eq!(decode_frame_header(&h), FrameHeader { opcode: b'D', config, path_len: len });
        assert_eq!(&h[1 + CONFIG_LEN..], &len.to_be_bytes());
        assert_eq!(decode_be_u32(&encode_be_u32(len)), len);
    }
}

/// The bytes of a listing of `(mode, oid digit, path)` records.
fn listing_bytes(records: &[(&str, u8, &[u8])]) -> std::vec::Vec<u8> {
    let mut bytes = std::vec::Vec::new();
    for (mode, digit, path) in records {
        bytes.extend_from_slice(mode.as_bytes());
        bytes.push(b' ');
        bytes.extend_from_slice(&[*digit; 40]);
        bytes.extend_from_slice(b" 0\t");
        bytes.extend_from_slice(path);
        bytes.push(0);
    }
    bytes
}

type Listing = (std::vec::Vec<u8>, std::vec::Vec<usize>);

/// A listing with unique paths in byte order, and its `ends`.
fn listing(records: &[(&str, u8, &[u8])]) -> Listing {
    let bytes = listing_bytes(records);
    let mut ends = std::vec![0; records.len()];
    assert!(parse_listing(&bytes, &mut ends, true));
    (bytes, ends)
}

/// The object order of a listing (by object id, then position).
fn order(l: &Listing) -> std::vec::Vec<usize> {
    let id = |j: usize| listing_fields(&l.0, &l.1, j).map(|f| l.0[f.start + OID_START..f.oid_end].to_vec()).unwrap();
    let mut order: std::vec::Vec<usize> = (0..l.1.len()).collect();
    order.sort_by_key(|j| (id(*j), *j));
    assert!(object_order_ok(&l.0, &l.1, &order));
    order
}

fn held(index: &Listing, other: &Listing) -> std::vec::Vec<bool> {
    let mut out = std::vec![true; index.1.len()];
    let wanted = std::vec![true; index.1.len()];
    assert!(held_entries(&index.0, &index.1, &wanted, &other.0, &other.1, &mut out));
    out
}

fn elsewhere(index: &Listing, i: usize, head: &Listing, parent: &Listing) -> bool {
    blob_elsewhere(&index.0, &index.1, &order(index), i, &head.0, &head.1, &order(head), &parent.0, &parent.1,
        &order(parent))
}

fn source(index: &Listing, i: usize, head: &Listing, from: usize) -> usize {
    next_move_source(&index.0, &index.1, i, &head.0, &head.1, &order(head), from)
}

#[test]
fn listings_are_parsed_exactly() {
    let (bytes, ends) = listing(&[("100644", b'a', b"x\ty"), ("120000", b'b', b"y/l")]);
    let first = listing_fields(&bytes, &ends, 0).unwrap();
    assert_eq!(&bytes[first.start + OID_START..first.oid_end], &[b'a'; 40]);
    assert_eq!(&bytes[first.path_start..first.end], b"x\ty");
    assert!(first.regular);
    let second = listing_fields(&bytes, &ends, 1).unwrap();
    assert_eq!(&bytes[second.path_start..second.end], b"y/l");
    assert!(!second.regular);
    assert_eq!(listing_fields(&bytes, &ends, 2), None);
    assert!(parse_listing(b"", &mut [], true));
    // Wrong count, truncated, extended, unmerged, bad object id, empty record.
    assert!(!parse_listing(&bytes, &mut [0; 1], true));
    assert!(!parse_listing(&bytes, &mut [0; 3], true));
    assert!(!parse_listing(&bytes[..bytes.len() - 1], &mut [0; 2], true));
    assert!(!parse_listing(&[&bytes[..], b"\0"].concat(), &mut [0; 2], true));
    let unmerged = [b"100644 ".as_slice(), &[b'a'; 40], b" 1\tx\0"].concat();
    assert!(!parse_listing(&unmerged, &mut [0; 1], true));
    let short = [b"100644 ".as_slice(), &[b'a'; 39], b" 0\tx\0"].concat();
    assert!(!parse_listing(&short, &mut [0; 1], true));
    let upper = [b"100644 ".as_slice(), &[b'A'; 40], b" 0\tx\0"].concat();
    assert!(!parse_listing(&upper, &mut [0; 1], true));
    assert!(!parse_listing(b"\0", &mut [0; 1], true));
}

#[test]
fn listings_are_in_path_order() {
    // Git's order is byte order of the whole path ("a-b" < "a.c" < "a/b" < "a0").
    for (a, b) in [(&b"a"[..], &b"b"[..]), (b"a", b"ab"), (b"", b"a"), (b"a-b", b"a.c"), (b"a.c", b"a/b"),
        (b"a/b", b"a0"), (b"a/b/c", b"a/bc"), (b"z\x7f", b"z\x80"), (b"A", b"a")]
    {
        assert!(bytes_lt(a, b) && !bytes_lt(b, a), "{a:?} {b:?}");
    }
    assert!(!bytes_lt(b"", b"") && !bytes_lt(b"a/b", b"a/b"));
    let mut ends = [0; 2];
    let sorted = listing_bytes(&[("100644", b'1', b"a.c"), ("100644", b'2', b"a/b")]);
    assert!(parse_listing(&sorted, &mut ends, true));
    // Out of order or a path twice (a crafted tree): refused, unless
    // repeated paths are allowed (the merged incoming commits).
    let swapped = listing_bytes(&[("100644", b'2', b"a/b"), ("100644", b'1', b"a.c")]);
    assert!(!parse_listing(&swapped, &mut ends, true));
    assert!(!parse_listing(&swapped, &mut ends, false));
    let twice = listing_bytes(&[("100644", b'1', b"a.secret"), ("100644", b'2', b"a.secret")]);
    assert!(!parse_listing(&twice, &mut ends, true));
    assert!(parse_listing(&twice, &mut ends, false));
    // In a merged listing, every record at a path is found.
    let index = listing(&[("100644", b'2', b"a.secret")]);
    let other = (twice, ends.to_vec());
    assert_eq!(held(&index, &other), [true]);
}

#[test]
fn object_orders_list_each_record_once_by_object_id() {
    let l = listing(&[("100644", b'2', b"a"), ("100644", b'1', b"b"), ("100644", b'2', b"c")]);
    assert_eq!(order(&l), [1, 0, 2]);
    for bad in [&[0usize, 1, 2][..], &[1, 2, 0], &[1, 0, 0], &[1, 0, 3], &[1, 0], &[1, 0, 2, 2]] {
        assert!(!object_order_ok(&l.0, &l.1, bad), "{bad:?}");
    }
    assert!(object_order_ok(b"", &[], &[]));
}

#[test]
fn snapshot_queries_compare_object_and_path() {
    let index = listing(&[("100644", b'1', b"a"), ("100644", b'2', b"b"), ("100644", b'3', b"c"),
        ("100644", b'4', b"moved")]);
    let head = listing(&[("100644", b'1', b"a"), ("100755", b'2', b"b"), ("100644", b'9', b"c"),
        ("100644", b'4', b"kept"), ("100644", b'4', b"moved"), ("100644", b'4', b"old")]);
    // The mode does not matter; another blob at the path is not held.
    assert_eq!(held(&index, &head), [true, true, false, true]);
    assert_eq!(held(&head, &index), [true, true, false, false, true, false]);
    let mut out = [true; 4];
    assert!(held_entries(&index.0, &index.1, &[false, true, true, false], &head.0, &head.1, &mut out));
    assert_eq!(out, [false, true, false, false]);
    assert!(!held_entries(&index.0, &index.1, &[true; 3], &head.0, &head.1, &mut out));
    let empty = listing(&[]);
    assert_eq!(held(&index, &empty), [false; 4]);
    // Move sources of `moved` (entry 3): the HEAD paths of its blob that
    // left the index, in HEAD order, never its own path.
    assert_eq!(source(&index, 3, &head, 0), 3);
    assert_eq!(source(&index, 3, &head, 4), 5);
    assert_eq!(source(&index, 3, &head, 6), 6);
    assert_eq!(source(&index, 0, &head, 0), 6);
    let kept = listing(&[("100644", b'4', b"kept"), ("100644", b'4', b"moved")]);
    assert_eq!(source(&kept, 1, &head, 0), 5);
    assert!(elsewhere(&index, 3, &empty, &head));
    assert!(!elsewhere(&index, 0, &head, &head));
    assert!(elsewhere(&kept, 1, &empty, &empty));
    // `local_change`: changed and known not to come from a commit, or forced plaintext.
    for (in_head, known, in_incoming, forced, envelope, expected) in [
        (false, true, false, false, true, true), (true, true, false, false, false, false),
        (false, false, false, false, true, false), (false, true, true, false, false, false),
        (true, true, true, true, false, true), (true, true, true, true, true, false),
    ] {
        assert_eq!(is_local_change(in_head, known, in_incoming, forced, envelope), expected);
    }
}

/// The queries agree with their definitions on random listings: held
/// (`Holds`), the keyless move check (`BlobElsewhere`) and move sources
/// (`MoveSource`, first from an offset).
#[test]
fn snapshot_queries_match_their_definitions() {
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = move |n: u64| { state ^= state << 13; state ^= state >> 7; state ^= state << 17; state % n };
    let names: [&[u8]; 8] = [b"a", b"a-b", b"a.c", b"a/b", b"a/b/c", b"a0", b"b", b"b\xc3\xa9"];
    for _ in 0..300 {
        let mut random = |size: u64| {
            let mut records: std::vec::Vec<(&str, u8, &[u8])> = std::vec::Vec::new();
            for name in names {
                if next(8) < size {
                    records.push(("100644", b'0' + next(4) as u8, name));
                }
            }
            listing(&records)
        };
        let (index, head, parent) = (random(6), random(5), random(3));
        let entries = |l: &Listing| (0..l.1.len()).map(|j| {
            let f = listing_fields(&l.0, &l.1, j).unwrap();
            (l.0[f.start + OID_START..f.oid_end].to_vec(), l.0[f.path_start..f.end].to_vec())
        }).collect::<std::vec::Vec<_>>();
        let (es, hs, ps) = (entries(&index), entries(&head), entries(&parent));
        let holds = |l: &[(std::vec::Vec<u8>, std::vec::Vec<u8>)], e: &(std::vec::Vec<u8>, std::vec::Vec<u8>)| l.contains(e);
        let expected: std::vec::Vec<bool> = es.iter().map(|e| holds(&hs, e)).collect();
        assert_eq!(held(&index, &head), expected);
        for (i, e) in es.iter().enumerate() {
            let other = |l: &[(std::vec::Vec<u8>, std::vec::Vec<u8>)]| l.iter().any(|x| x.0 == e.0 && x.1 != e.1);
            assert_eq!(elsewhere(&index, i, &head, &parent), other(&es) || other(&hs) || other(&ps));
            for from in 0..=hs.len() {
                let first = (from..hs.len()).find(|j| hs[*j].0 == e.0 && hs[*j].1 != e.1 && !holds(&es, &hs[*j]));
                assert_eq!(source(&index, i, &head, from), first.unwrap_or(hs.len()));
            }
        }
    }
}

/// Lookups stay fast on large listings where nothing matches (a whole
/// directory rewritten): every query is a binary search, not a scan.
#[test]
fn snapshot_queries_scale_to_large_listings() {
    let n = 50_000;
    let names: std::vec::Vec<std::vec::Vec<u8>> = (0..n).map(|i| std::format!("d/f{i:06}").into_bytes()).collect();
    let build = |digit: u8| {
        let records: std::vec::Vec<(&str, u8, &[u8])> = names.iter().map(|p| ("100644", digit, p.as_slice())).collect();
        listing(&records)
    };
    let (index, head) = (build(b'1'), build(b'2'));
    let (index_order, head_order) = (order(&index), order(&head));
    let started = std::time::Instant::now();
    assert!(held(&index, &head).iter().all(|h| !h));
    for i in (0..n).step_by(7) {
        assert!(blob_elsewhere(&index.0, &index.1, &index_order, i, &head.0, &head.1, &head_order, &head.0,
            &head.1, &head_order));
        assert_eq!(next_move_source(&index.0, &index.1, i, &head.0, &head.1, &head_order, 0), n);
    }
    // Quadratic lookups take minutes here.
    assert!(started.elapsed() < std::time::Duration::from_secs(20), "{:?}", started.elapsed());
}

#[test]
fn listing_attributes_and_selectability() {
    let (bytes, ends) = listing(&[("100644", b'c', b".gitattributes"), ("100644", b'a', b"a.env"),
        ("120000", b'b', b"link"), ("100755", b'd', b"run")]);
    let response = b".gitattributes\0filter\0unset\0a.env\0filter\0transcrypt-v3\0link\0filter\0unspecified\0run\0filter\0transcrypt-v3\0";
    let mut flags = [false; 4];
    assert!(parse_listing_attrs(&bytes, &ends, response, &mut flags));
    assert_eq!(flags, [false, true, false, true]);
    assert_eq!(first_unselectable(&bytes, &ends, &flags), 4);
    assert_eq!(first_unselectable(&bytes, &ends, &[false, true, true, true]), 2);
    assert_eq!(first_unselectable(&bytes, &ends, &[true, false, false, false]), 0);
    assert!(!parse_listing_attrs(&bytes, &ends, &response[..response.len() - 1], &mut flags));
    assert!(!parse_listing_attrs(&bytes, &ends, &[&response[..], b"x"].concat(), &mut flags));
    assert!(!parse_listing_attrs(&bytes, &ends, response, &mut [false; 3]));
    let swapped = b"a.env\0filter\0transcrypt-v3\0.gitattributes\0filter\0unset\0link\0filter\0unspecified\0run\0filter\0transcrypt-v3\0";
    assert!(!parse_listing_attrs(&bytes, &ends, swapped, &mut flags));
}

#[test]
fn stored_keys_unlock_only_their_own_authentic_config() {
    let config = [7u8; CONFIG_LEN];
    let mut file = std::vec::Vec::from(&config[..]);
    file.extend_from_slice(&[1u8; KEY_LEN]);
    assert_eq!(stored_key_state(true, &file, &config, true), StoredKey::Unlocked);
    assert_eq!(stored_key_state(true, &file, &config, false), StoredKey::Stale);
    let mut other = config;
    other[54] = 8;
    assert_eq!(stored_key_state(true, &file, &other, true), StoredKey::Stale);
    assert_eq!(stored_key_state(false, &file, &config, true), StoredKey::Absent);
    assert_eq!(stored_key_state(true, &[1u8; KEY_LEN], &config, true), StoredKey::Absent);
    for n in [0, 1, KEY_LEN + 1, KEY_FILE_LEN - 1, KEY_FILE_LEN + 1] {
        assert_eq!(stored_key_state(true, &std::vec![0u8; n], &config, true), StoredKey::Damaged, "{n}");
    }
}

#[test]
fn batch_headers_name_the_object_and_a_canonical_size() {
    let oid = b"0123456789abcdef0123456789abcdef01234567";
    let header = |rest: &str| [oid.as_slice(), rest.as_bytes()].concat();
    assert_eq!(parse_batch_header(&header(" blob 12\n"), oid), Some(12));
    assert_eq!(parse_batch_header(&header(" blob 0\n"), oid), Some(0));
    assert_eq!(parse_batch_header(&header(" blob 9999999999999999999\n"), oid), Some(9_999_999_999_999_999_999));
    for bad in [" blob 012\n", " blob 00\n", " blob +12\n", " blob 12", " blob \n", " tree 12\n", " missing\n",
                " blob 1 2\n", " blob 12\n\n", " blob 10000000000000000000\n", "  blob 12\n"] {
        assert_eq!(parse_batch_header(&header(bad), oid), None, "{bad:?}");
    }
    let mut other = *oid;
    other[0] = b'f';
    assert_eq!(parse_batch_header(&header(" blob 12\n"), &other), None);
    assert_eq!(parse_batch_header(b"", oid), None);
    assert_eq!(blob_read(MAX_RECORD as u64, false), BlobRead::Read);
    assert_eq!(blob_read(MAX_RECORD as u64 + 1, true), BlobRead::Skip);
    assert_eq!(blob_read(u64::MAX, false), BlobRead::TooLarge);
}
