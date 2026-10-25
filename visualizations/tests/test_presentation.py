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

    def test_beat_slideshow_and_embedded_segment_clips(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)
            sample=path/'clean-0.mp4'
            data=b'fake-section-mp4-bytes-for-tests-only'
            sample.write_bytes(data)
            deck=load_slides()
            clean = next(s for s in deck.slides if s.id=='clean')
            self.assertGreater(len(clean.beat_names),2)
            intro = next(s for s in deck.slides if s.id=='intro')
            self.assertEqual(len(intro.beat_names),1)
            html_file=render_html(deck,path/'embedded.html',
                                  segments={'clean':{clean.beat_names[0]:sample}},
                                  embed_videos=True)
            html=html_file.read_text()
            self.assertIn('data:video/mp4;base64,' + base64.b64encode(data).decode(),html)
            self.assertIn('id="step-data"',html)
            self.assertIn('id="video-data"',html)
            self.assertIn('class="scene-video"',html)
            self.assertIn('layout-cinema',html)
            self.assertIn('layout-evidence',html)
            self.assertIn('layout-statement',html)
            self.assertIn('LEAN: IF REALIZES',html)
            self.assertIn('TRUSTED: CRYPTO',html)
            self.assertIn('requestFullscreen',html)
            self.assertIn('ArrowRight',html)
            self.assertIn('event.code === \'Space\'',html)
            self.assertIn('next beat',html)
            self.assertNotIn(' controls playsinline',html)
            self.assertNotIn('https://',html)
            self.assertNotIn('http://',html)
            self.assertNotIn('file://',html)
            self.assertNotIn(str(path),html)
            notes=write_speaker_notes(deck,path/'speaker-notes.md').read_text()
            self.assertIn('open_record_spec',notes)
            self.assertIn('Realizes',notes)

    def test_html_sidecars_and_missing_media_keep_clickable_svg_steps(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)
            videos=path/'videos'; videos.mkdir()
            sample=videos/'clone-beat.mp4'; sample.write_bytes(b'video-data')
            deck=load_slides()
            clone = next(s for s in deck.slides if s.id=='clone')
            html=render_html(deck,path/'index.html',
                             segments={'clone':{clone.beat_names[0]:sample}}).read_text()
            self.assertIn('videos/clone-beat.mp4',html)
            self.assertIn('SVG beat snapshots',html)
            self.assertIn('data:image/svg+xml;base64,',html)
            self.assertIn('data-role="beat-caption"',html)
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
