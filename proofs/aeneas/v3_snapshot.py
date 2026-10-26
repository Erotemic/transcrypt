#!/usr/bin/env python3
"""Tracked production v3 Charon/Aeneas snapshot: verify, compare, refresh.

No generated build outputs, dependencies, external Python packages, or secrets
are committed. The manifest binds the exact *production* Rust source and the
Aeneas-generated Lean definitions. Verification is an integrity requirement;
Lean refinement proofs must be compiled separately.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
SNAP = Path('proofs/aeneas/v3')
GENERATED = Path('rust/proofs/aeneas/generated/V3Core/lean')
MANIFEST = 'SNAPSHOT.json'
SOURCE = (
    'rust/crates/transcrypt-v3-core/src/lib.rs',
    'rust/crates/transcrypt-v3-core/Cargo.toml',
    'rust/crates/transcrypt-v3-core/hax.toml',
)
HAX_OWNED = (
    'V3Wire/Extraction.lean',
    'V3Wire/Extraction/Funs.lean',
    'V3Wire/Extraction/Types.lean',
    'V3Wire/Extraction/FunsExternal.lean',
    'V3Wire/Extraction/FunsExternal_Template.lean',
)
ASSUMPTIONS = ('V3Wire/Assumptions/FunsExternal.lean',)
REVIEW_ONLY = ('V3Wire/Extraction/FunsExternal.lean',
               'V3Wire/Extraction/FunsExternal_Template.lean')
PROJECT_CONFIG = ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json')
PINS = {
    'cargo_hax': '0.4.2',
    'charon': 'nightly-2026.09.02',
    'aeneas': 'build-183e4f0',
    'lean': 'leanprover/lean4:v4.31.0',
    'hax_lean_lib': 'v0.3.30',
}
# Exact production entrypoints; regenerated source must contain all of them.
ENTRYPOINTS = (
    'decode_config_exact', 'encode_config',
    'decode_file_header_exact', 'encode_file_header',
    'parse_config', 'parse_file_header',
    'is_canonical_protected_path', 'initialize_config', 'authenticate_config',
    'seal_record', 'open_record', 'hydrate_action', 'lock_action',
    'authorize_agent_request', 'parse_attr_record', 'parse_attr_response', 'smudge_action', 'seal_action', 'parse_index_entry',
    'encode_frame_header', 'decode_frame_header',
    'is_object_id', 'record_envelope_ok', 'decode_pkt_len',
    'parse_listing', 'listing_fields', 'held_entries', 'is_local_change',
    'next_move_source', 'blob_elsewhere', 'parse_listing_attrs', 'first_unselectable',
    'stored_key_state', 'parse_batch_header', 'blob_read',
)
BAD = re.compile(r'\b(?:sorry|admit|axiom|native_decide|bv_decide)\b')


class SnapshotError(ValueError):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_file(root: Path, relative: str) -> bytes:
    p = root / relative
    if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(root.resolve()):
        raise SnapshotError(f'Missing or unsafe snapshot input: {p}')
    return p.read_bytes()


def check_generated_shape(root: Path) -> None:
    extraction = root / 'V3Wire/Extraction'
    found = {p.relative_to(root).as_posix() for p in extraction.glob('*.lean')}
    expected = {p for p in HAX_OWNED if p.startswith('V3Wire/Extraction/')}
    if found != expected:
        raise SnapshotError(f'Extraction file set differs: missing={expected-found}, extra={found-expected}')
    # More files under extraction must never be ignored by an allowlist.
    if any(p.is_file() or p.is_symlink() for p in extraction.rglob('*') if p.parent != extraction):
        raise SnapshotError('Unexpected nested Aeneas extraction files')
    funcs = safe_file(root, 'V3Wire/Extraction/Funs.lean').decode('utf-8')
    for name in ENTRYPOINTS:
        if not re.search(r'(?m)^def ' + name + r'\s', funcs):
            raise SnapshotError(f'Missing extracted production entrypoint: {name}')
    types = safe_file(root, 'V3Wire/Extraction/Types.lean').decode('utf-8')
    for name in ('Config', 'FormatError', 'Refusal', 'V3Primitives'):
        if not re.search(r'(?m)^(?:structure|inductive) ' + name + r'\s', types):
            raise SnapshotError(f'Missing extracted production type: {name}')


def no_lean_holes(root: Path, files: tuple[str, ...]) -> None:
    # Lex comments/strings as the existing proof-tree checker does. The
    # synthetic ZIP's template comments are not interpreted as declarations.
    from check_v3_proof_tree import strip_lean_comments_and_strings
    for name in files:
        content = safe_file(root, name).decode('utf-8')
        stripped = strip_lean_comments_and_strings(content)
        bad = BAD.search(stripped)
        if bad:
            line = stripped.count('\n', 0, bad.start()) + 1
            raise SnapshotError(f'Admitted code in {root / name}:{line}')


def source_hashes(root: Path) -> dict[str, str]:
    return {name: digest(safe_file(root, name)) for name in SOURCE}


def read_manifest(root: Path) -> dict:
    raw = safe_file(root / SNAP, MANIFEST)
    data = json.loads(raw)
    if data.get('format') != 1 or data.get('pins') != PINS:
        raise SnapshotError('Unrecognized generator version pins/manifest schema')
    if set(data.get('sources', {})) != set(SOURCE):
        raise SnapshotError('Incomplete or expanded Rust source manifest')
    if set(data.get('generated', {})) != set(HAX_OWNED + ASSUMPTIONS + PROJECT_CONFIG):
        raise SnapshotError('Incomplete or expanded generated-file manifest')
    return data


def verify(root: Path) -> None:
    snap = root / SNAP
    data = read_manifest(root)
    for source, expected in data['sources'].items():
        actual = digest(safe_file(root, source))
        if actual != expected:
            raise SnapshotError(f'Rust source changed since extraction: {source}')
    for name, expected in data['generated'].items():
        actual = digest(safe_file(snap, name))
        if actual != expected:
            raise SnapshotError(f'Checked-in Aeneas file differs: {name}')
    if safe_file(snap, 'lean-toolchain').decode().strip() != PINS['lean']:
        raise SnapshotError('Lean toolchain is not pinned as reviewed')
    cfg = safe_file(snap, 'lakefile.toml').decode()
    for needle in (PINS['aeneas'], PINS['hax_lean_lib'], 'name = "Transcrypt"'):
        if needle not in cfg:
            raise SnapshotError(f'Unpinned or missing Lake package: {needle}')
    check_generated_shape(snap)
    proofs = tuple(sorted(p.relative_to(snap).as_posix()
                          for p in (snap / 'V3Wire/Verification').glob('*.lean')))
    no_lean_holes(snap, HAX_OWNED + ASSUMPTIONS + ('V3Wire.lean',) + proofs)


def check_regenerated_toolchain(root: Path, generated: Path) -> None:
    # Hax emits an *unprepared* Lake project. Our tracked Lake file also has
    # the independent Transcrypt library appended by prepare-v3-refinement.sh;
    # comparison of the two files byte-for-byte would always fail.
    lean = safe_file(generated, 'lean-toolchain')
    if lean != safe_file(root / SNAP, 'lean-toolchain'):
        raise SnapshotError('Managed translator changed the pinned Lean toolchain')
    cfg = safe_file(generated, 'lakefile.toml').decode('utf-8')
    for required in (PINS['aeneas'], PINS['hax_lean_lib']):
        if required not in cfg:
            raise SnapshotError(f'Managed translator changed an Aeneas dependency: {required}')
    # A fresh output may not have a resolved lake-manifest.json until Lake
    # runs; when present it must agree on pinned cryptographic-proof deps.
    manifest = generated / 'lake-manifest.json'
    if manifest.exists():
        if manifest.is_symlink():
            raise SnapshotError('Symlink in newly generated Lake manifest')
        package_data = json.loads(manifest.read_text())
        reviewed_data = json.loads(safe_file(root / SNAP, 'lake-manifest.json'))
        def core_pins(data: dict) -> dict:
            return {p['name']: p['rev'] for p in data['packages']
                    if p['name'] in ('aeneas', 'hax', 'mathlib')}
        if core_pins(package_data) != core_pins(reviewed_data):
            raise SnapshotError('Managed translator changed pinned Lake dependencies')


def compare(root: Path) -> None:
    verify(root)
    generated = root / GENERATED
    check_generated_shape(generated)
    check_regenerated_toolchain(root, generated)
    for name in HAX_OWNED:
        if safe_file(root / SNAP, name) != safe_file(generated, name):
            raise SnapshotError(f'Regenerated Aeneas output differs: {name}')
    # Assumptions are user-maintained and can only be accepted after review.
    if safe_file(generated, ASSUMPTIONS[0]) != safe_file(root / SNAP, ASSUMPTIONS[0]):
        raise SnapshotError('Regenerated external assumptions differ; review the trust boundary')
    provenance = generated.parent / 'PROVENANCE.txt'
    if provenance.is_file():
        proof = provenance.read_text(encoding='utf-8')
        for name in SOURCE[:1] + SOURCE[2:3]:
            line = f'{digest(safe_file(root, name))}  {name}'
            if line not in proof.splitlines():
                raise SnapshotError(f'Generated provenance does not bind current source: {name}')
        for key in (PINS['cargo_hax'], PINS['aeneas'], PINS['charon']):
            if key not in proof:
                raise SnapshotError(f'Missing version in regeneration provenance: {key}')
    # Do not require PROVENANCE in the unit-test fixture: mock output lacks
    # it. The real translate-v3-core.sh always writes it or returns nonzero.


def refresh(root: Path) -> None:
    snap, generated = root / SNAP, root / GENERATED
    check_generated_shape(generated)
    check_regenerated_toolchain(root, generated)
    # Never auto-import new assumptions, external templates or toolchain.
    for name in ASSUMPTIONS + REVIEW_ONLY:
        if safe_file(snap, name) != safe_file(generated, name):
            raise SnapshotError(f'Generator dependency/assumption changed: {name}; review before refresh')
    no_lean_holes(generated, HAX_OWNED + ASSUMPTIONS)
    for name in HAX_OWNED:
        (snap / name).write_bytes(safe_file(generated, name))
    save_manifest(root)
    verify(root)


def save_manifest(root: Path) -> None:
    snap = root / SNAP
    data = {
        'format': 1,
        'purpose': 'Production Rust v3 wire-codec generated Lean, not a crypto proof',
        'pins': PINS,
        'sources': source_hashes(root),
        'generated': {name: digest(safe_file(snap, name))
                      for name in HAX_OWNED + ASSUMPTIONS + PROJECT_CONFIG},
    }
    (snap / MANIFEST).write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def stage_spec(root: Path) -> None:
    verify(root)
    target = root / SNAP
    sources = (
        ('proofs/lean/Transcrypt/V3Wire.lean', 'Transcrypt/V3Wire.lean'),
        ('proofs/lean/Transcrypt/V3WireCodec.lean', 'Transcrypt/V3WireCodec.lean'),
        ('proofs/lean/Transcrypt/V3Policy.lean', 'Transcrypt/V3Policy.lean'),
    )
    for name, dst in sources:
        data = safe_file(root, name)
        destination = target / dst
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.is_symlink():
            raise SnapshotError(f'Refusing symlink for staged spec: {destination}')
        destination.write_bytes(data)
    (target / 'Transcrypt.lean').write_text('import Transcrypt.V3WireCodec\nimport Transcrypt.V3Policy\n')
    # This is a copy of the exact independent spec, never a second authority.
    for name, dst in sources:
        if safe_file(root, name) != safe_file(target, dst):
            raise SnapshotError(f'Staged Lean spec diverged from authoritative source: {name}')
    no_lean_holes(target, tuple(dst for _, dst in sources))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['verify', 'compare', 'refresh', 'stage'])
    parser.add_argument('--root', type=Path, default=ROOT)
    options = parser.parse_args()
    root = options.root.resolve()
    try:
        if options.action == 'verify':
            verify(root)
        elif options.action == 'compare':
            compare(root)
        elif options.action == 'refresh':
            refresh(root)
        else:
            stage_spec(root)
    except (SnapshotError, OSError, ValueError, UnicodeError) as exc:
        print(f'v3 Aeneas snapshot {options.action} FAILED: {exc}', file=sys.stderr)
        return 1
    print(f'v3 Aeneas snapshot {options.action}: OK')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
