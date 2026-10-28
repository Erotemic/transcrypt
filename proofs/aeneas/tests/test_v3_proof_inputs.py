#!/usr/bin/env python3
"""Offline proof-input integrity tests; no Cargo, Lean, or mocked proof claims."""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'proofs/aeneas'))
from check_v3_proof_tree import ProofTreeError, check, strip_lean_comments_and_strings
from export_v3_proof_inputs import create_bundle


class ProofInputTests(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory()
        self.addCleanup(self.workspace.cleanup)
        # Resolved: on macOS the temporary directory is under a symlink.
        self.root = Path(self.workspace.name).resolve()
        self.project = self.root / 'rust/proofs/aeneas/generated/V3Core/lean'
        self.provenance = self.project.parent / 'PROVENANCE.txt'
        self.project.joinpath('V3Wire/Extraction').mkdir(parents=True)
        self.project.joinpath('V3Wire/Verification').mkdir(parents=True)
        self.project.joinpath('Transcrypt').mkdir()
        self.root.joinpath('proofs/lean/Transcrypt').mkdir(parents=True)
        self.root.joinpath('docs/verification/specs').mkdir(parents=True)
        self.root.joinpath('docs/verification/reference').mkdir(parents=True)
        self.root.joinpath('rust/crates/transcrypt-v3-core/src').mkdir(parents=True)
        for relative, data in {
            'rust/crates/transcrypt-v3-core/src/lib.rs': b'pub fn actual_production_core() {}\n',
            'rust/crates/transcrypt-v3-core/hax.toml': b'[scenario.v3-wire]\nbackend="lean"\n',
            'rust/crates/transcrypt-v3-core/Cargo.toml': b'[package]\nname="a"\n',
            'proofs/lean/Transcrypt/V3Wire.lean': b'namespace Transcrypt.V3Wire\ndef foo := 1\nend Transcrypt.V3Wire\n',
            'proofs/lean/Transcrypt/V3WireCodec.lean': b'import Transcrypt.V3Wire\n',
            'docs/verification/specs/V3-AUTHENTICATED-P0.md': b'# only public format\n',
            'docs/verification/reference/v3-core-traceability.md': b'# trace\n',
            'rust/proofs/aeneas/generated/V3Core/lean/V3Wire/Extraction/Funs.lean':
                b'def decode_config_exact := true\ndef encode_config := true\n',
            'rust/proofs/aeneas/generated/V3Core/lean/V3Wire/Extraction.lean': b'import V3Wire.Extraction.Funs\n',
            'rust/proofs/aeneas/generated/V3Core/lean/V3Wire.lean':
                b'import V3Wire.Extraction\nimport V3Wire.Verification.IndependentSpec\n',
            'rust/proofs/aeneas/generated/V3Core/lean/V3Wire/Verification/IndependentSpec.lean':
                b'import V3Wire.Extraction\nimport Transcrypt.V3WireCodec\n',
            'rust/proofs/aeneas/generated/V3Core/lean/Transcrypt.lean':
                b'import Transcrypt.V3WireCodec\n',
            'rust/proofs/aeneas/generated/V3Core/lean/lakefile.toml':
                b'name="v3"\n[[lean_lib]]\nname="Transcrypt"\n',
            'rust/proofs/aeneas/generated/V3Core/lean/lean-toolchain':
                b'leanprover/lean4:v4.33.0\n',
        }.items():
            output = self.root / relative
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(data)
        for spec in ['V3Wire.lean', 'V3WireCodec.lean']:
            (self.project / 'Transcrypt' / spec).write_bytes(
                (self.root / 'proofs/lean/Transcrypt' / spec).read_bytes())
        sources = ['rust/crates/transcrypt-v3-core/src/lib.rs',
                   'rust/crates/transcrypt-v3-core/hax.toml']
        tracked_generated = [
            self.project / 'V3Wire/Extraction.lean',
            self.project / 'V3Wire/Extraction/Funs.lean',
        ]
        self.provenance.write_text(''.join(
            hashlib.sha256((self.root / source).read_bytes()).hexdigest() + '  ' + source + '\n'
            for source in sources) + ''.join(
            hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + str(path) + '\n'
            for path in tracked_generated))

    def test_import_graph_and_source_binding(self):
        files = check(self.root, self.project)
        self.assertEqual(len(files), 7)
        (self.root / 'rust/crates/transcrypt-v3-core/src/lib.rs').write_text('changed')
        with self.assertRaisesRegex(ProofTreeError, 'Stale extraction'):
            check(self.root, self.project)

    def test_imported_admissions_rejected(self):
        original = self.project / 'V3Wire/Extraction/Funs.lean'
        original.write_text(original.read_text() + 'theorem bogus : False := by sorry\n')
        with self.assertRaisesRegex(ProofTreeError, 'Admitted code'):
            check(self.root, self.project)

    def test_nested_comments_strings_not_falsely_admitted(self):
        extra = self.project / 'V3Wire/Extraction/Funs.lean'
        extra.write_text(extra.read_text() + '/- axiom /- sorry -/ admit -/\n'
                         'def word : String := "sorry axiom admit"\n-- sorry\n')
        # This test models output originally emitted by the translator, not a
        # post-extraction edit; the provenance digest must match the new text.
        lines = self.provenance.read_text().splitlines()
        self.provenance.write_text('\n'.join(
            hashlib.sha256(extra.read_bytes()).hexdigest() + '  ' + str(extra)
            if line.endswith('  ' + str(extra)) else line
            for line in lines) + '\n')
        self.assertGreaterEqual(len(check(self.root, self.project)), 6)
        self.assertEqual(strip_lean_comments_and_strings('/- sorry -/\n-- admit\n'), '\n\n')

    def test_unimported_template_is_not_a_trusted_proof(self):
        template = self.project / 'V3Wire/Extraction/FunsExternal_Template.lean'
        template.write_text('theorem template : False := by sorry\n')
        with self.provenance.open('a') as stream:
            stream.write(hashlib.sha256(template.read_bytes()).hexdigest() + '  ' + str(template) + '\n')
        self.assertTrue(check(self.root, self.project))
        self.assertNotIn(template, check(self.root, self.project))

    def test_generated_lean_modification_rejected_even_without_admission(self):
        generated = self.project / 'V3Wire/Extraction/Funs.lean'
        generated.write_text(generated.read_text() + '\ndef injected_but_well_typed := 1\n')
        with self.assertRaisesRegex(ProofTreeError, 'changed since translation'):
            check(self.root, self.project)

    def test_generated_lean_aggregate_modification_rejected(self):
        aggregate = self.project / 'V3Wire/Extraction.lean'
        aggregate.write_text(aggregate.read_text() + '\n-- unexpected edit\n')
        with self.assertRaisesRegex(ProofTreeError, 'changed since translation'):
            check(self.root, self.project)

    def test_imported_root_tampering_rejected(self):
        (self.project / 'V3Wire.lean').write_text('import V3Wire.Extraction\n')
        with self.assertRaisesRegex(ProofTreeError, 'independent spec is not imported'):
            check(self.root, self.project)

    def test_independent_spec_must_be_exact_copy(self):
        (self.project / 'Transcrypt/V3Wire.lean').write_text('def foo := 2\n')
        with self.assertRaisesRegex(ProofTreeError, 'not staged verbatim'):
            check(self.root, self.project)

    def test_generated_source_symlinks_rejected(self):
        file = self.project / 'V3Wire/Extraction/Funs.lean'
        elsewhere = self.root / 'other.lean'
        elsewhere.write_bytes(file.read_bytes())
        file.unlink()
        file.symlink_to(elsewhere)
        with self.assertRaisesRegex(ProofTreeError, 'Symlink'):
            check(self.root, self.project)

    def test_proof_input_zip_is_allowlisted_and_deterministic(self):
        (self.project / '.lake/build/lib/lean').mkdir(parents=True)
        (self.project / '.lake/build/lib/lean/not-included.olean').write_text('never')
        dep = self.project / '.lake/packages/aeneas/Aeneas/Unreviewed.lean'
        dep.parent.mkdir(parents=True)
        dep.write_text('theorem should_not_export : False := by sorry\n')
        first = self.root / 'bundle1.zip'
        second = self.root / 'bundle2.zip'
        count1, digest1 = create_bundle(self.root, first)
        count2, digest2 = create_bundle(self.root, second)
        self.assertEqual((count1, digest1), (count2, digest2))
        with zipfile.ZipFile(first) as archive:
            names = archive.namelist()
            self.assertIn('PROOF-INPUTS-SHA256.txt', names)
            self.assertIn('rust/proofs/aeneas/generated/V3Core/lean/V3Wire/Extraction/Funs.lean', names)
            self.assertNotIn('.lake/build/lib/lean/not-included.olean', names)
            self.assertFalse(any('/.lake/' in entry for entry in names))
            self.assertNotIn('rust/proofs/aeneas/generated/V3Core/lean/.lake/packages/aeneas/Aeneas/Unreviewed.lean', names)
            self.assertEqual(archive.testzip(), None)
            for entry in archive.read('PROOF-INPUTS-SHA256.txt').decode().splitlines():
                digest, filename = entry.split('  ', 1)
                self.assertEqual(digest, hashlib.sha256(archive.read(filename)).hexdigest())

    def test_export_refuses_stale_source(self):
        (self.root / 'rust/crates/transcrypt-v3-core/hax.toml').write_text('modified')
        with self.assertRaisesRegex(ProofTreeError, 'Stale extraction'):
            create_bundle(self.root, self.root / 'bad.zip')


if __name__ == '__main__':
    unittest.main()
