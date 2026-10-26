"""Avoid turning the verified-core milestone into an unscoped app claim."""
from pathlib import Path
import unittest

from tvis.catalog import REPO_ROOT, get_scene, validate_catalog
from tvis.slide_deck import load_slides
from tvis.svg_preview import render_svg


class AssuranceStatusTests(unittest.TestCase):
    def test_checkpoint_scoped_to_actual_roadmap(self):
        roadmap = (REPO_ROOT / 'docs/verification/V3-ROADMAP.md').read_text()
        self.assertIn('P6: release qualification', roadmap)
        self.assertIn('R-01', roadmap)
        self.assertIn('parse_attr_response', (
            REPO_ROOT / 'proofs/aeneas/v3/PROOF-STATUS.md').read_text())
        scene = get_scene('status')
        self.assertIn('P0-P5', scene.claim)
        self.assertIn('R-01', scene.claim)
        self.assertIn('V7', scene.claim)
        plan = scene.diagram()
        self.assertEqual(plan.node_map()['core'].evidence.level, 'source-proof')
        self.assertEqual(plan.node_map()['models'].evidence.level, 'model-proof')
        self.assertEqual(plan.node_map()['product'].evidence.level, 'tested')
        self.assertEqual(plan.node_map()['review'].evidence.level, 'planned')
        self.assertIn('R-01', plan.beats[-1].caption)
        self.assertNotEqual(plan.beats[-1].status, 'proved')
        self.assertIn('review pending', get_scene('roadmap').diagram().beats[0].knowledge[1].items[1])

    def test_a4_debts_do_not_masquerade_as_core_theorems(self):
        plan = get_scene('adapter').diagram()
        levels = {key: node.evidence.level for key, node in plan.node_map().items()}
        self.assertEqual(levels, {
            'git': 'trusted-platform',
            'parser': 'source-proof',
            'adapter': 'tested',
            'gate': 'source-proof',
        })
        self.assertEqual(plan.node_map()['gate'].evidence.basis, 'seal_action_spec')
        stages = {b.key: b for b in plan.beats}
        self.assertEqual(stages['provenance'].status, 'tested')
        self.assertEqual(stages['decision'].status, 'proved')
        self.assertEqual(stages['credential'].status, 'tested')
        self.assertEqual(stages['effects'].status, 'tested')
        self.assertEqual(stages['target'].status, 'planned')
        self.assertIn('cat-file --batch', stages['object'].caption)
        self.assertIn('A17', stages['credential'].caption)
        self.assertIn('A8/A12', stages['effects'].caption)
        rendered = render_svg(plan, beat='decision')
        self.assertIn('data-evidence="source-proof"', rendered)
        self.assertIn('data-evidence="tested"', rendered)

    def test_two_new_beat_slides_are_renderable_without_manim(self):
        scenes = validate_catalog()
        self.assertEqual(len(scenes), 20)
        slides = load_slides().slides
        self.assertEqual(len(slides), 22)
        targets = {s.id: s for s in slides}
        for name, scene_id in (('milestones', 'status'),
                               ('adapter-correspondence', 'adapter')):
            slide = targets[name]
            self.assertEqual(slide.scene.id, scene_id)
            self.assertEqual(slide.steps, 'all')
            self.assertGreater(len(slide.beat_names), 3)
            self.assertIn(slide.beat, slide.diagram.beat_names())
        self.assertEqual(targets['milestones'].layout, 'evidence')
        self.assertEqual(targets['adapter-correspondence'].layout, 'cinema')
        self.assertIn('88001fd', load_slides().footer)


if __name__ == '__main__':
    unittest.main()
