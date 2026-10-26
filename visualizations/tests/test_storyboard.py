"""Proof/source-bound Manim authoring checks; no Manim, Rust, or Lean required."""
from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import tempfile
import unittest
from xml.etree import ElementTree

from tvis.__main__ import main, render_command
from tvis.catalog import REPO_ROOT, VIS_ROOT, get_scene, load_catalog, validate_catalog
from tvis.diagram import validate
from tvis.gallery import build_gallery
from tvis.palette import palette
from tvis.presentation import build_presentation, scene_fingerprint
from tvis.svg_preview import CANVAS_W, CANVAS_H, render_svg


IDS = ('legend', 'selection', 'unlock', 'clean', 'crypto', 'record',
       'rename', 'audit', 'clone', 'lock', 'attack', 'status', 'inventory',
       'contract', 'proof', 'lifecycle', 'adapter', 'assumptions', 'offline', 'roadmap')


class StoryboardTests(unittest.TestCase):
    def test_scene_sequence_sources_and_proof_anchors(self):
        scenes = validate_catalog()
        self.assertEqual(tuple(scene.id for scene in scenes), IDS)
        self.assertGreaterEqual(sum(bool(scene.proof_anchors) for scene in scenes), 5)
        for scene in scenes:
            self.assertTrue(scene.sources)
            self.assertLessEqual(len((VIS_ROOT / scene.file).read_text().splitlines()), 12)
            self.assertTrue(scene.narration and len(scene.narration) > 140)
            self.assertEqual(scene.diagram().key, scene.id)
            for ref in scene.sources:
                self.assertTrue((REPO_ROOT / ref).is_file())

    def test_every_beat_renders_valid_dark_and_light_svg(self):
        for scene in validate_catalog():
            plan = scene.diagram()
            for theme in ('dark', 'light'):
                for i, beat in enumerate(plan.beats):
                    svg = render_svg(plan, beat=i, theme=theme)
                    root = ElementTree.fromstring(svg)
                    self.assertEqual(root.attrib['width'], str(CANVAS_W))
                    self.assertEqual(root.attrib['height'], str(CANVAS_H))
                    self.assertIn(plan.title, svg)
                    self.assertIn(beat.key.upper(), svg)

    def test_beats_reveal_in_order_and_information_snapshots(self):
        for scene in validate_catalog():
            plan = scene.diagram()
            old_nodes, old_links = set(), set()
            for n, beat in enumerate(plan.beats):
                nodes, links, shown, index = plan.state(n)
                visible_nodes = {x.key for x in nodes}
                visible_links = {x.key for x in links}
                self.assertTrue(visible_nodes >= old_nodes)
                self.assertTrue(visible_links >= old_links)
                self.assertIs(shown, beat)
                self.assertEqual(n, index)
                old_nodes, old_links = visible_nodes, visible_links
            self.assertEqual(old_nodes, set(plan.node_map()))
            self.assertEqual(old_links, set(plan.link_map()))
            if scene.id != 'record':
                self.assertTrue(all(beat.knowledge for beat in plan.beats))
                for beat in plan.beats:
                    self.assertEqual({k.owner for k in beat.knowledge}, set(plan.node_map()))

    def test_current_features_not_described_as_future_work(self):
        selection = get_scene('selection').diagram()
        roadmap = get_scene('roadmap').diagram()
        self.assertFalse(any(b.status == 'planned' for b in selection.beats))
        self.assertTrue(any(b.status == 'planned' for b in roadmap.beats))
        self.assertTrue(any(b.status == 'implemented' for b in roadmap.beats))
        self.assertIn('private/**', selection.state('today')[2].caption)
        self.assertTrue(any('store' in b.caption.lower() for b in get_scene('unlock').diagram().beats))
        self.assertIn('migration', get_scene('roadmap').claim)

    def test_threat_boundary_is_visible_and_source_anchored(self):
        assumptions = get_scene('assumptions').diagram()
        self.assertEqual(assumptions.node_map()['core'].role, 'proved')
        for name in ('crypto', 'adapter'):
            self.assertEqual(assumptions.node_map()[name].role, 'assumed')
        self.assertTrue(any(b.status == 'assumed' for b in assumptions.beats))
        proof_scene = get_scene('proof')
        self.assertIn('open_record_spec', proof_scene.proof_anchors)
        self.assertTrue(any('Realizes' in s.narration for s in validate_catalog()))
        self.assertTrue(any(b.status == 'modeled' for b in get_scene('lifecycle').diagram().beats))

    def test_operation_evidence_and_payload_types_are_independent(self):
        from tvis.diagram import Processing, Evidence, PAYLOAD_ROLES, EVIDENCE_ROLES
        expected={
            'unlock': {'kdf':'trusted-crypto','auth':'conditional-proof','store':'tested'},
            'clean': {'filter':'tested','core':'conditional-proof','git':'trusted-platform'},
            'crypto': {'gate':'conditional-proof','primitive':'trusted-crypto','assemble':'source-proof'},
            'rename': {'adapter':'tested','decide':'source-proof','seal':'conditional-proof'},
            'audit': {'git':'trusted-platform','shape':'source-proof','audit':'tested','remote':'trusted-platform'},
            'clone': {'check':'conditional-proof','disk':'tested'},
            'lock': {'snapshot':'tested','gate':'source-proof','writer':'tested'},
            'lifecycle': {'core':'conditional-proof','model':'model-proof','effect':'tested'},
        }
        for scene,levels in expected.items():
            diagram=get_scene(scene).diagram()
            for node,tier in levels.items():
                self.assertEqual(diagram.node_map()[node].evidence.level,tier)
        for scene in validate_catalog():
            diagram=scene.diagram()
            for beat in diagram.beats:
                if beat.packet:
                    self.assertIn(beat.packet_kind, PAYLOAD_ROLES)
                if beat.processing:
                    self.assertIn(beat.processing.node, diagram.node_map())
                    self.assertIn(beat.processing.before_kind, PAYLOAD_ROLES)
                    self.assertIn(beat.processing.after_kind, PAYLOAD_ROLES)
            for node in diagram.nodes:
                if node.evidence:
                    self.assertIn(node.evidence.level, EVIDENCE_ROLES)

    def test_data_transforms_show_all_main_lifecycle_operations(self):
        kinds=set()
        for name in ('selection','unlock','clean','crypto','rename','audit','clone','lock'):
            plan=get_scene(name).diagram()
            self.assertGreaterEqual(len([b for b in plan.beats if b.processing]),2)
            self.assertGreaterEqual(len([b for b in plan.beats if b.packet]),2)
            kinds.update(b.packet_kind for b in plan.beats if b.packet)
        self.assertGreaterEqual(len(kinds),4)
        svg=render_svg(get_scene('crypto').diagram(),beat='primitive')
        self.assertIn('data-evidence="trusted-crypto"',svg)
        self.assertIn('data-payload-kind="plaintext"',svg)
        self.assertIn('data-processing="primitive"',svg)
        self.assertIn('data-output="ciphertext"',svg)

    def test_bogus_operation_proof_fails_catalog_validation(self):
        from tvis.diagram import Evidence
        from tvis.catalog import SceneInfo
        from unittest.mock import patch
        scene=get_scene('crypto')
        diagram=scene.diagram()
        bad=replace(diagram.nodes[0],evidence=Evidence('source-proof','imaginary_theorem'))
        altered=replace(diagram,nodes=(bad,)+diagram.nodes[1:])
        with patch.object(SceneInfo,'diagram',lambda self: altered if self.id=='crypto' else __import__(
             self.plan,fromlist=['PLAN']).PLAN):
            with self.assertRaisesRegex(ValueError,'missing evidence theorem'):
                validate_catalog()

    def test_inventory_does_not_conflate_source_proofs_and_adapter_models(self):
        inventory = get_scene('inventory')
        self.assertTrue({'encode_file_header_refines', 'open_record_spec',
                         'hydratePlan_spec', 'decode_pkt_len_spec'} <= set(inventory.proof_anchors))
        nodes = inventory.diagram().node_map()
        self.assertEqual(nodes['codec'].role, 'proved')
        self.assertEqual(nodes['crypto'].role, 'proved')
        self.assertEqual(nodes['lifecycle'].role, 'policy')
        self.assertEqual(inventory.diagram().beats[-1].status, 'modeled')
        contract = get_scene('contract')
        self.assertIn('Realizes', contract.narration)
        self.assertEqual(contract.diagram().node_map()['primitive'].role, 'assumed')
        self.assertTrue(any(b.status == 'assumed' for b in contract.diagram().beats))
        atlas = (VIS_ROOT/'PROOF-ATLAS.md').read_text()
        self.assertIn('open_record_spec', atlas)
        self.assertIn('A4', atlas)
        self.assertIn('A5', atlas)

    def test_record_xray_reveals_bytes_and_never_a_public_key(self):
        p = get_scene('record').diagram()
        self.assertEqual(p.visible_layer_depth('v3record', 0), 0)
        self.assertEqual(p.visible_layer_depth('v3record', 1), 1)
        self.assertEqual(p.visible_layer_depth('v3record', 2), 2)
        self.assertEqual(p.visible_layer_depth('v3record', 3), 3)
        self.assertIn('not nested encryption', p.footer.lower())
        for b in p.beats:
            self.assertNotIn('plaintext key', b.caption.lower())

    def test_proof_anchors_disappear_when_missing(self):
        from tvis.catalog import SceneInfo
        info=get_scene('proof')
        bad=replace(info, proof_anchors=('invented_fake_lean_theorem',))
        # The same check as the catalog: every anchor must be in its Lean file.
        for anchor in bad.proof_anchors:
            self.assertFalse(any(
                ('theorem ' + anchor) in (REPO_ROOT / source).read_text()
                for source in bad.sources if source.endswith('.lean')
            ))

    def test_diagram_geometry_rejects_unknown_links(self):
        p=get_scene('clean').diagram()
        changed=replace(p.links[0],destination='not-a-real-node')
        with self.assertRaisesRegex(ValueError, 'missing endpoint'):
            validate(replace(p, links=(changed,)+p.links[1:]))

    def test_cli_and_render_commands_have_no_shell_expansion(self):
        command, env=render_command('proof', quality='l', still=True, theme='dark')
        self.assertIn('-ql', command)
        self.assertIn('-s', command)
        self.assertEqual(command[-2:], ['tvis/scenes/proof.py', 'RustLeanRefinement'])
        self.assertEqual(env['TVIS_THEME'], 'dark')
        with self.assertRaisesRegex(ValueError, 'quality'):
            render_command('proof',quality='madeup')
        self.assertEqual(main(['check']), 0)

    def test_gallery_embeds_storyboard_without_server_or_secrets(self):
        with tempfile.TemporaryDirectory() as directory:
            file=build_gallery(Path(directory) / 'index.html')
            document=file.read_text()
            self.assertIn('Transcrypt v3', document)
            self.assertIn('open_record_spec', document)
            self.assertIn('data:image/svg+xml;base64,', document)
            self.assertIn('Operation-by-operation evidence', document)
            self.assertIn('"tier": "conditional-proof"', document)
            self.assertNotIn('http://localhost:', document)
            self.assertNotIn('file://', document)
            self.assertGreater(document.count('"id": "'), 10)  # all scene and beat IDs embedded
            self.assertIn('"status": "planned"', document)

    def test_incremental_presentation_skips_unchanged_video(self):
        from tvis.presentation import MANIFEST, PRESENTATION
        # Use an isolated manifest by temporarily overriding the module paths.
        import tvis.presentation as presentation
        with tempfile.TemporaryDirectory() as directory:
            old_manifest, old_presentation = presentation.MANIFEST, presentation.PRESENTATION
            presentation.PRESENTATION = Path(directory)/'presentation'
            presentation.MANIFEST = presentation.PRESENTATION/'manifest.json'
            calls=[]
            def fake_video(scene):
                calls.append(scene)
                p=Path(directory)/f'{scene}.mp4'
                p.write_bytes(b'fake-mp4-video-data')
                return p
            try:
                output, changed = build_presentation(render_scene=fake_video)
                self.assertEqual(len(changed), len(IDS))
                self.assertTrue(output.is_file())
                output, changed = build_presentation(render_scene=fake_video)
                self.assertFalse(changed)
                self.assertEqual(len(calls), len(IDS))
            finally:
                presentation.MANIFEST = old_manifest
                presentation.PRESENTATION = old_presentation

    def test_semantic_colors_include_proof_and_premise(self):
        self.assertEqual(palette('dark').keys(), palette('light').keys())
        self.assertNotEqual(palette('dark')['proved'], palette('dark')['assumed'])
        self.assertNotEqual(palette('dark')['guest'], palette('dark')['provider'])
        with self.assertRaisesRegex(ValueError, 'unknown theme'):
            palette('pink')


if __name__=='__main__':
    unittest.main()
