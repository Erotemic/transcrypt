#!/usr/bin/env python3
"""Verify generated v3 proof input provenance and imported Lean source hygiene.

This is a packaging/build integrity gate, not a model checker or a proof of
Rust/Lean correspondence. No external Python packages or runtime dependencies.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import sys


SOURCE_RELATIVE = (
    'rust/crates/transcrypt-v3-core/src/lib.rs',
    'rust/crates/transcrypt-v3-core/hax.toml',
)
SPEC_RELATIVE = (
    'Transcrypt/V3Wire.lean',
    'Transcrypt/V3WireCodec.lean',
)
BAD_DECLARATION = re.compile(r'\b(sorry|admit|axiom)\b')
IMPORT_LINE = re.compile(r'^\s*import\s+(.+?)\s*$')
HASH_LINE = re.compile(r'^([a-f0-9]{64})\s+(.+)$')


class ProofTreeError(ValueError):
    pass


def hash_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strip_lean_comments_and_strings(text: str) -> str:
    """Remove nested Lean block comments, line comments, and literals.

    Preserve newlines to report meaningful source locations. An unfinished
    comment/string is a hard error, not a way to hide an admitted declaration.
    """
    result: list[str] = []
    pos = 0
    n = len(text)
    nesting = 0
    in_string = False
    while pos < n:
        current = text[pos]
        ahead = text[pos:pos+2]
        if nesting:
            if ahead == '/-':
                nesting += 1
                pos += 2
            elif ahead == '-/':
                nesting -= 1
                pos += 2
            else:
                if current == '\n':
                    result.append('\n')
                pos += 1
            continue
        if in_string:
            if current == '\\':
                pos += 2
                continue
            if current == '"':
                in_string = False
            if current == '\n':
                result.append('\n')
            pos += 1
            continue
        if ahead == '/-':
            nesting = 1
            pos += 2
        elif ahead == '--':
            eol = text.find('\n', pos)
            if eol < 0:
                break
            result.append('\n')
            pos = eol + 1
        elif current == '"':
            in_string = True
            pos += 1
        else:
            result.append(current)
            pos += 1
    if nesting or in_string:
        raise ProofTreeError('unterminated Lean comment or string literal')
    return ''.join(result)


def check(root: Path, project: Path) -> list[Path]:
    root = root.resolve()
    project = project.resolve()
    generated_dir = root / 'rust/proofs/aeneas/generated/V3Core'
    if project != generated_dir / 'lean':
        raise ProofTreeError(f'Unexpected generated project path: {project}')
    provenance = generated_dir / 'PROVENANCE.txt'
    if not provenance.is_file():
        raise ProofTreeError(f'Missing extraction provenance: {provenance}')
    raw_provenance = provenance.read_text(encoding='utf-8')
    provenance_entries = {}
    for line in raw_provenance.splitlines():
        match = HASH_LINE.fullmatch(line.strip())
        if match:
            digest, name = match.groups()
            if name in provenance_entries and provenance_entries[name] != digest:
                raise ProofTreeError(f'Conflicting extraction hash for {name}')
            provenance_entries[name] = digest
    for relative in SOURCE_RELATIVE:
        expected = hash_bytes((root / relative).read_bytes())
        if provenance_entries.get(relative) != expected:
            raise ProofTreeError(f'Stale extraction for {relative}; rerun translate-v3-core.sh')

    for relative in SPEC_RELATIVE:
        source = root / 'proofs/lean' / relative
        staged = project / relative
        if not staged.is_file() or source.read_bytes() != staged.read_bytes():
            raise ProofTreeError(f'Independent spec not staged verbatim: {relative}')

    if (project / 'Transcrypt.lean').read_text(encoding='utf-8').strip() != 'import Transcrypt.V3WireCodec':
        raise ProofTreeError('Generated Transcrypt root must import only the independent v3 spec')

    for needed in (
        'V3Wire.lean',
        'V3Wire/Extraction.lean',
        'V3Wire/Verification/IndependentSpec.lean',
    ):
        if not (project / needed).is_file():
            raise ProofTreeError(f'Missing import root: {needed}')
    compiled: set[Path] = set()
    pending: list[Path] = [project / 'V3Wire.lean', project / 'Transcrypt.lean']
    while pending:
        source = pending.pop()
        if source in compiled:
            continue
        if source.is_symlink():
            raise ProofTreeError(f'Symlink in proof source: {source}')
        if not source.is_file() or not source.resolve().is_relative_to(project):
            raise ProofTreeError(f'Unsafe imported Lean source: {source}')
        compiled.add(source)
        body = strip_lean_comments_and_strings(source.read_text(encoding='utf-8'))
        bad = BAD_DECLARATION.search(body)
        if bad is not None:
            line = body.count('\n', 0, bad.start()) + 1
            raise ProofTreeError(f'Admitted code in imported module: {source.relative_to(project)}:{line}: {bad.group()}')
        for line in body.splitlines():
            found = IMPORT_LINE.match(line)
            if not found:
                continue
            for module in found.group(1).split():
                candidate = project / (module.replace('.', '/') + '.lean')
                if candidate.is_file() or module.startswith(('V3Wire.', 'Transcrypt.')):
                    if not candidate.is_file():
                        raise ProofTreeError(f'Missing imported local Lean module: {module}')
                    pending.append(candidate)
    if not (project / 'V3Wire/Extraction.lean') in compiled:
        raise ProofTreeError('Generated Rust code is not imported by the Lean root')
    if not (project / 'V3Wire/Verification/IndependentSpec.lean') in compiled:
        raise ProofTreeError('The independent spec is not imported by the Lean root')
    if not any(path.is_relative_to(project / 'V3Wire/Extraction') for path in compiled):
        raise ProofTreeError('No actual Aeneas-generated function module is imported')

    # Re-check the actual emitted Lean bytes, not just the original Rust bytes.
    # The extraction script signs every hax-owned module in PROVENANCE.txt,
    # including the aggregate V3Wire/Extraction.lean, before user proof files
    # are staged. User-managed Verification/ modules are intentionally separate.
    extraction = project / 'V3Wire/Extraction'
    hax_owned = {project / 'V3Wire/Extraction.lean'}
    hax_owned.update(extraction.rglob('*.lean'))
    if len(hax_owned) < 2:
        raise ProofTreeError('No generated function files to verify')
    for source in sorted(hax_owned):
        if source.is_symlink() or not source.resolve().is_relative_to(project):
            raise ProofTreeError(f'Unsafe generated Lean path: {source}')
        if not source.is_file():
            raise ProofTreeError(f'Missing generated Lean source: {source}')
        expected = provenance_entries.get(str(source))
        actual = hash_bytes(source.read_bytes())
        if expected != actual:
            raise ProofTreeError(f'Generated Lean source changed since translation: {source.relative_to(project)}')
    expected_files = {Path(name) for name in provenance_entries
                      if name.startswith(str(extraction) + '/') and name.endswith('.lean')}
    if expected_files != (hax_owned - {project / 'V3Wire/Extraction.lean'}):
        raise ProofTreeError('Generated Lean file set differs from extraction provenance')
    return sorted(compiled)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    root = args.root.resolve()
    project = root / 'rust/proofs/aeneas/generated/V3Core/lean'
    try:
        modules = check(root, project)
    except (ProofTreeError, OSError, UnicodeError) as ex:
        print(f'v3 proof source gate failed: {ex}', file=sys.stderr)
        return 1
    print(f'Checked {len(modules)} imported project-local Lean modules against Rust source and independent spec.')
    print('This is an integrity gate, not a refinement proof.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
