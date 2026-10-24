#!/usr/bin/env python3
"""Integrity and regen-gate tests for the tracked real Aeneas snapshot."""
from __future__ import annotations

from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'proofs/aeneas'))
from v3_snapshot import (
    SnapshotError, SOURCE, HAX_OWNED, ASSUMPTIONS, PROJECT_CONFIG,
    GENERATED, SNAP, verify, compare, stage_spec, refresh,
)


class TrackedV3Tests(unittest.TestCase):
    def setUp(self) -> None:
        context = tempfile.TemporaryDirectory()
        self.addCleanup(context.cleanup)
        self.root = Path(context.name)
        # Copy only the public source/snapshot inputs actually used by the gate.
        paths = list(SOURCE) + [
            'proofs/lean/Transcrypt/V3Wire.lean',
            'proofs/lean/Transcrypt/V3WireCodec.lean',
        ]
        for name in paths:
            dest = self.root / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, dest)
        shutil.copytree(ROOT / SNAP, self.root / SNAP)

    def regenerated(self) -> Path:
        dst = self.root / GENERATED
        for name in HAX_OWNED + ASSUMPTIONS + PROJECT_CONFIG:
            output = dst / name
            output.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.root / SNAP / name, output)
        return dst

    def test_real_uploaded_source_and_snapshot_bound_together(self) -> None:
        verify(self.root)
        stage_spec(self.root)
        for name in ('V3Wire.lean', 'V3WireCodec.lean'):
            self.assertEqual((self.root / SNAP / 'Transcrypt' / name).read_bytes(),
                             (self.root / 'proofs/lean/Transcrypt' / name).read_bytes())
        self.assertEqual((self.root / SNAP / 'Transcrypt.lean').read_text(),
                         'import Transcrypt.V3WireCodec\n')

    def test_source_change_requires_real_regeneration(self) -> None:
        path = self.root / SOURCE[0]
        path.write_bytes(path.read_bytes() + b'\n// changed wire semantics\n')
        with self.assertRaisesRegex(SnapshotError, 'Rust source changed'):
            verify(self.root)

    def test_generated_proof_file_mutation_rejected(self) -> None:
        file = self.root / SNAP / 'V3Wire/Extraction/Funs.lean'
        file.write_bytes(file.read_bytes().replace(b'84#u8', b'88#u8', 1))
        with self.assertRaisesRegex(SnapshotError, 'Aeneas file differs'):
            verify(self.root)

    def test_generator_pin_mutation_rejected(self) -> None:
        file = self.root / SNAP / 'lean-toolchain'
        file.write_text('leanprover/lean4:v4.33.0\n')
        with self.assertRaisesRegex(SnapshotError, 'Aeneas file differs'):
            verify(self.root)

    def test_any_new_untracked_extraction_source_fails_closed(self) -> None:
        path = self.root / SNAP / 'V3Wire/Extraction/Unexpected.lean'
        path.write_text('def bypass := true\n')
        with self.assertRaisesRegex(SnapshotError, 'file set differs'):
            verify(self.root)

    def test_external_assumption_modification_rejected(self) -> None:
        file = self.root / SNAP / ASSUMPTIONS[0]
        file.write_text(file.read_text() + '\naxiom everything_is_true : False\n')
        with self.assertRaisesRegex(SnapshotError, 'Aeneas file differs'):
            verify(self.root)

    def test_review_gate_refuses_admitted_refinement(self) -> None:
        file = self.root / SNAP / 'V3Wire/Verification/Refinement.lean'
        file.write_text(file.read_text() + '\ntheorem imaginary : False := by sorry\n')
        with self.assertRaisesRegex(SnapshotError, 'Admitted code'):
            verify(self.root)

    def test_cached_dependency_not_exported_as_snapshot(self) -> None:
        nested = self.root / SNAP / '.lake/packages/mathlib/Mathlib/Random.lean'
        nested.parent.mkdir(parents=True)
        nested.write_text('axiom imported : False\n')
        verify(self.root)  # Build caches are intentionally never snapshot inputs.

    def test_unprepared_hax_project_without_lake_manifest_is_comparable(self) -> None:
        generated = self.regenerated()
        # hax writes just its own dependencies. Our preparation script later
        # adds the independent specification's Lean library.
        config = generated / 'lakefile.toml'
        text = config.read_text()
        text = text[:text.index('# Independent v3 protocol specification')]
        config.write_text(text)
        (generated / 'lake-manifest.json').unlink()
        compare(self.root)

    def test_generated_drift_rejected_and_refresh_is_explicit(self) -> None:
        generated = self.regenerated()
        compare(self.root)
        output = generated / HAX_OWNED[1]
        output.write_bytes(output.read_bytes() + b'\n-- extraction changed\n')
        with self.assertRaisesRegex(SnapshotError, 'Regenerated Aeneas output differs'):
            compare(self.root)
        refresh(self.root)
        compare(self.root)

    def test_refresh_never_accepts_external_assumption_edits(self) -> None:
        generated = self.regenerated()
        path = generated / ASSUMPTIONS[0]
        path.write_bytes(path.read_bytes() + b'\n-- changed assumptions\n')
        with self.assertRaisesRegex(SnapshotError, 'Generator dependency/assumption changed'):
            refresh(self.root)

    def test_refresh_never_silently_adopts_new_external_templates(self) -> None:
        generated = self.regenerated()
        path = generated / 'V3Wire/Extraction/FunsExternal_Template.lean'
        path.write_bytes(path.read_bytes() + b'\n-- new external dependency\n')
        with self.assertRaisesRegex(SnapshotError, 'Generator dependency/assumption changed'):
            refresh(self.root)

    def test_ignored_generated_build_cannot_supply_new_entries(self) -> None:
        generated = self.regenerated()
        (generated / 'V3Wire/Extraction/Unexpected.lean').write_text('def maybe := true\n')
        with self.assertRaisesRegex(SnapshotError, 'file set differs'):
            compare(self.root)

    def test_staged_spec_is_not_a_second_authority(self) -> None:
        stage_spec(self.root)
        file = self.root / SNAP / 'Transcrypt/V3WireCodec.lean'
        file.write_text('def unintendedFork := 1\n')
        stage_spec(self.root)
        self.assertEqual(file.read_bytes(),
                         (self.root / 'proofs/lean/Transcrypt/V3WireCodec.lean').read_bytes())

    def test_no_symlinks_accepted_from_generated_source(self) -> None:
        file = self.root / SNAP / HAX_OWNED[0]
        target = self.root / 'outside.lean'
        target.write_bytes(file.read_bytes())
        file.unlink()
        file.symlink_to(target)
        with self.assertRaisesRegex(SnapshotError, 'Missing or unsafe'):
            verify(self.root)


if __name__ == '__main__':
    unittest.main()
