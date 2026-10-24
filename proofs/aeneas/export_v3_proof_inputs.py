#!/usr/bin/env python3
"""Reproducible, allowlisted ZIP of real generated v3 Lean proof inputs.

Use this to transfer the actual Aeneas-generated functions to a proof author
without exporting the user's Git repository, key socket, decrypted files, or
other unrelated artifacts. This does not imply a compiled refinement proof.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys
import zipfile

from check_v3_proof_tree import check, ProofTreeError


SOURCE = [
    'rust/crates/transcrypt-v3-core/src/lib.rs',
    'rust/crates/transcrypt-v3-core/Cargo.toml',
    'rust/crates/transcrypt-v3-core/hax.toml',
    'proofs/lean/Transcrypt/V3Wire.lean',
    'proofs/lean/Transcrypt/V3WireCodec.lean',
    'docs/verification/specs/V3-AUTHENTICATED-P0.md',
    'docs/verification/reference/v3-core-traceability.md',
    'rust/proofs/aeneas/generated/V3Core/PROVENANCE.txt',
]
GEN_PREFIX = 'rust/proofs/aeneas/generated/V3Core/lean/'


def create_bundle(root: Path, destination: Path) -> tuple[int, str]:
    root = root.resolve()
    project = root / GEN_PREFIX
    modules = check(root, project)
    selected = {root / name for name in SOURCE}
    selected.update(modules)
    selected.update(project / name for name in ('lakefile.toml', 'lean-toolchain'))
    manifest = project / 'lake-manifest.json'
    if manifest.is_file():
        selected.add(manifest)
    # Include unimported model templates as evidence for proof authors: they
    # can reveal missing external specifications, but are NOT counted as proofs.
    selected.update(path for path in project.rglob('*.lean') if path.is_file())
    content = []
    for file in sorted(selected):
        if file.is_symlink() or not file.resolve().is_relative_to(root):
            raise ProofTreeError(f'Refusing symlink or outside path in bundle: {file}')
        if not file.is_file():
            raise ProofTreeError(f'Missing required proof input: {file}')
        name = file.relative_to(root).as_posix()
        content.append((name, file.read_bytes()))
    digest_lines = [hashlib.sha256(data).hexdigest() + '  ' + name
                    for name, data in content]
    content.append(('PROOF-INPUTS-SHA256.txt', ('\n'.join(digest_lines) + '\n').encode()))
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, 'w') as archive:
        for name, data in content:
            info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = (0o100644 << 16)
            archive.writestr(info, data, compresslevel=9)
    with zipfile.ZipFile(destination) as archive:
        failed = archive.testzip()
        if failed:
            raise ProofTreeError(f'ZIP failed integrity check: {failed}')
    checksum = hashlib.sha256(destination.read_bytes()).hexdigest()
    return len(content), checksum


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path, required=True)
    opts = parser.parse_args()
    try:
        count, digest = create_bundle(opts.root, opts.output.expanduser().resolve())
    except (ProofTreeError, OSError, UnicodeError) as exc:
        print(f'Could not export generated Lean proof inputs: {exc}', file=sys.stderr)
        return 1
    print(f'Exported {count} strictly allowlisted proof input files: {opts.output}')
    print(f'SHA-256: {digest}')
    print('Bundle is restricted to code/proof inputs, not worktree secret files or agent state.')
    print('Generated Lean extraction has NOT yet been proved equivalent to the independent spec.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
