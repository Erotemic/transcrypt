"""No-Manim presentation tests, including inline MP4 and PDF static fallback."""
from __future__ import annotations

import base64
import importlib.util
from pathlib import Path
import tempfile
import unittest

from tvis.slide_deck import load_slides, render_html, write_speaker_notes


class PresentationTests(unittest.TestCase):
    def test_mixed_layouts_and_named_beats(self):
        deck=load_slides()
        self.assertEqual(len(deck.slides),20)
        self.assertEqual({slide.layout for slide in deck.slides},
                         {'cover','cinema','split','diagram','evidence','statement'})
        for slide in deck.slides:
            self.assertTrue(slide.scene.diagram().state(slide.beat))
            self.assertTrue(slide.title)
        self.assertEqual(next(s for s in deck.slides if s.id=='sealing').active_operation,
                         'primitive')
        self.assertEqual(next(s for s in deck.slides if s.id=='unlock').active_operation,
                         'store')

    def test_self_contained_html_with_embedded_clip_and_source_notes(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)
            sample=path/'clean.mp4'
            data=b'fake-mp4-bytes-for-tests-only'
            sample.write_bytes(data)
            deck=load_slides()
            html_file=render_html(deck,path/'embedded.html',videos={'clean':sample},embed_videos=True)
            html=html_file.read_text()
            self.assertIn('data:video/mp4;base64,' + base64.b64encode(data).decode(),html)
            self.assertIn('data-scene="clean"',html)
            self.assertIn('class="scene-video"',html)
            self.assertIn('layout-cinema',html)
            self.assertIn('layout-evidence',html)
            self.assertIn('layout-statement',html)
            self.assertIn('LEAN: IF REALIZES',html)
            self.assertIn('TRUSTED: CRYPTO',html)
            self.assertIn('requestFullscreen',html)
            self.assertIn('ArrowRight',html)
            self.assertNotIn('https://',html)
            self.assertNotIn('http://',html)
            self.assertNotIn('file://',html)
            self.assertNotIn(str(path),html)
            notes=write_speaker_notes(deck,path/'speaker-notes.md').read_text()
            self.assertIn('open_record_spec',notes)
            self.assertIn('Realizes',notes)

    def test_html_sidecars_and_missing_media_degrade_to_exact_diagram(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)
            videos=path/'videos'; videos.mkdir()
            (videos/'clone.mp4').write_bytes(b'video-data')
            deck=load_slides()
            html=render_html(deck,path/'index.html',videos={'clone':videos/'clone.mp4'}).read_text()
            self.assertIn('videos/clone.mp4',html)
            self.assertIn('Static beat · render Manim to enable motion',html)
            self.assertIn('data:image/svg+xml;base64,',html)
            self.assertNotIn('data:video/mp4;base64,',html)
            self.assertIn('data-slide-id="trust-boundary"',html)

    def test_bad_slide_beat_is_rejected(self):
        from tvis.slide_deck import load_slides
        from tvis.slide_deck import SLIDES_FILE
        source=SLIDES_FILE.read_text()
        with tempfile.TemporaryDirectory() as folder:
            bad=Path(folder)/'bad.toml'
            bad.write_text(source.replace('beat = "commit"','beat = "invented-beat"',1))
            with self.assertRaisesRegex(ValueError,'unknown beat'):
                load_slides(bad)

    @unittest.skipUnless(importlib.util.find_spec('reportlab') and importlib.util.find_spec('cairosvg'),
                         'optional PDF presentation libraries not installed')
    def test_pdf_pages_are_16_9_and_have_link_annotation(self):
        from tvis.pdf_slides import render_pdf, PAGE_W, PAGE_H
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'presentation.pdf'
            deck=load_slides()
            render_pdf(deck,path,video_scenes={'clean'})
            self.assertGreater(path.stat().st_size,50_000)
            if importlib.util.find_spec('pypdf'):
                from pypdf import PdfReader
                doc=PdfReader(str(path))
                self.assertEqual(len(doc.pages),len(deck.slides))
                for page in doc.pages:
                    self.assertEqual(tuple(round(float(x)) for x in page.mediabox[2:]),
                                     (PAGE_W,PAGE_H))
                annotations=[a.get_object().get('/A') for a in doc.pages[4]['/Annots']]
                self.assertTrue(any('index.html#slide-clean' in str(a) for a in annotations))
            else:
                self.assertTrue(path.read_bytes().startswith(b'%PDF-'))


if __name__=='__main__':
    unittest.main()
