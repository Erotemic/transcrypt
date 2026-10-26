"""Targeted scene and static export paths must avoid full video rendering."""
from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tvis.__main__ import main, render_command
from tvis.catalog import VIS_ROOT
from tvis.presentation import publish_scene
from tvis.slide_deck import load_slides, select_slides


class FastBuildTests(unittest.TestCase):
    def test_filtered_slides_keep_authored_order_and_refuse_typos(self):
        deck = load_slides()
        chosen = select_slides(deck, scene_ids=('crypto', 'clean'))
        self.assertEqual([slide.id for slide in chosen.slides],
                         ['intro', 'clean', 'sealing', 'closing'])
        self.assertEqual([slide.id for slide in select_slides(deck, slide_ids=('sealing',)).slides],
                         ['sealing'])
        self.assertEqual(len(deck.slides), 22)
        with self.assertRaisesRegex(ValueError, 'unknown scene'):
            select_slides(deck, scene_ids=('does-not-exist',))
        with self.assertRaisesRegex(ValueError, 'unknown slide'):
            select_slides(deck, slide_ids=('does-not-exist',))
        with self.assertRaisesRegex(ValueError, 'either scenes or slides'):
            select_slides(deck, scene_ids=('clean',), slide_ids=('sealing',))

    def test_pdf_only_skips_gallery_html_notes_and_manim(self):
        import tvis.presentation as presentation
        with tempfile.TemporaryDirectory() as d:
            folder = Path(d)
            original = presentation.PRESENTATION
            presentation.PRESENTATION = folder
            def fake_pdf(deck, target, **kwargs):
                self.assertEqual([s.id for s in deck.slides], ['unlock'])
                self.assertEqual(kwargs['html_name'], 'index-unlock.html')
                target.write_bytes(b'%PDF-1.4\n')
                return target
            try:
                with (patch('tvis.presentation.render_html', side_effect=AssertionError('HTML built')),
                      patch('tvis.presentation.build_gallery', side_effect=AssertionError('Gallery built')),
                      patch('tvis.presentation.write_speaker_notes', side_effect=AssertionError('Notes built')),
                      patch('tvis.pdf_slides.render_pdf', side_effect=fake_pdf)):
                    outputs = presentation.export_presentation(formats='pdf', scene_ids=('unlock',))
                self.assertEqual(tuple(outputs), ('pdf',))
                self.assertEqual(outputs['pdf'].name, 'presentation-unlock.pdf')
                self.assertFalse((folder/'index-unlock.html').exists())
            finally:
                presentation.PRESENTATION = original

    def test_targeted_publish_reuses_a_clip_then_force_refreshes_only_it(self):
        import tvis.presentation as presentation
        with tempfile.TemporaryDirectory() as d:
            folder = Path(d)
            original = presentation.PRESENTATION, presentation.MANIFEST
            presentation.PRESENTATION = folder/'presentation'
            presentation.MANIFEST = presentation.PRESENTATION/'manifest.json'
            calls=[]
            def renderer(name):
                calls.append(name)
                p=folder/'fresh.mp4'
                p.write_bytes(b'a-full-scene-MP4-placeholder')
                return p
            try:
                path, changed=publish_scene('unlock', render_scene=renderer)
                self.assertTrue(changed)
                self.assertEqual(path.read_bytes(), b'a-full-scene-MP4-placeholder')
                path, changed=publish_scene('unlock', render_scene=renderer)
                self.assertFalse(changed)
                self.assertEqual(calls, ['unlock'])
                path, changed=publish_scene('unlock', force=True, render_scene=renderer)
                self.assertTrue(changed)
                self.assertEqual(calls, ['unlock','unlock'])
                # `all` can use this same manifest, avoiding a second unlock render.
                # Other scenes are allowed to render in a subsequent `all` build.
                from json import loads
                manifest=loads(presentation.MANIFEST.read_text())
                self.assertIn('unlock', manifest['clips'])
                output = presentation.export_presentation(
                    formats='html', scene_ids=('unlock',))
                html = output['html'].read_text()
                self.assertIn('id="step-data"', html)
                self.assertIn('data-scene="unlock"', html)
                self.assertNotIn('videos/unlock.mp4', html)  # monolithic video not used
            finally:
                presentation.PRESENTATION, presentation.MANIFEST = original

    def test_publish_refuses_partial_clip_and_cache_is_default(self):
        command, _ = render_command('unlock')
        self.assertNotIn('--disable_caching', command)
        command, _ = render_command('unlock', no_cache=True)
        self.assertIn('--disable_caching', command)
        self.assertEqual(main(['render','unlock','--publish','--still']), 2)
        self.assertEqual(main(['render','unlock','--publish','--animation','1,2']), 2)
        command, _ = render_command('unlock', save_sections=True)
        self.assertIn('--save_sections',command)
        with self.assertRaisesRegex(ValueError,'complete video'):
            render_command('unlock', still=True, save_sections=True)

    @unittest.skipUnless(shutil.which('make'), 'make is not installed')
    def test_make_pdf_and_one_scene_are_independent(self):
        def dry(*args):
            run=subprocess.run(('make','-n',*args),cwd=VIS_ROOT,
                               capture_output=True,text=True,check=True)
            return run.stdout
        pdf=dry('pdf')
        self.assertIn('--format pdf',pdf)
        self.assertNotIn(' -m tvis all',pdf)
        self.assertNotIn(' -m tvis render',pdf)
        filtered=dry('pdf','SCENE=unlock')
        self.assertIn('--scene unlock',filtered)
        scene=dry('scene','SCENE=unlock')
        self.assertIn('render unlock --publish',scene)
        self.assertNotIn(' -m tvis all',scene)
        standalone=dry('standalone','SLIDE=sealing')
        self.assertIn('--embed-videos',standalone)
        self.assertIn('--slide sealing',standalone)


if __name__ == '__main__':
    unittest.main()
