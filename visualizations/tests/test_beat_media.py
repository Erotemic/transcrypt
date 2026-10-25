"""Section clips use one MP4 per named Manim beat, not whole-scene playback."""
from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from tvis.beat_media import stage_sections, published_sections, _read_source_sections
from tvis.catalog import get_scene
from tvis.presentation import scene_fingerprint
from tvis.slide_deck import render_html, select_slides, load_slides


class BeatMediaTests(unittest.TestCase):
    def build_fixture(self, root: Path, scene_id: str = 'unlock') -> Path:
        source = root / 'sections'
        source.mkdir()
        entries = [{'name': 'autocreated', 'video': 'intro.mp4'}]
        (source / 'intro.mp4').write_bytes(b'intro')
        for i, beat in enumerate(get_scene(scene_id).diagram().beats):
            name = f'{i:04d}.mp4'
            (source / name).write_bytes(b'beat-' + beat.key.encode())
            entries.append({'name': beat.key, 'video': name})
        index = source / f'{scene_id}.json'
        index.write_text(json.dumps(entries))
        return index

    def test_publish_and_load_all_beats_with_trustworthy_fingerprint(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            index = self.build_fixture(root)
            destination = root / 'published'
            fingerprint = scene_fingerprint(get_scene('unlock'),
                                            quality='l', theme='dark', speed=1.0)
            count = stage_sections('unlock', target=destination, quality='l',
                                   theme='dark', speed=1, fingerprint=fingerprint,
                                   media_dir=root, section_index=index)
            self.assertEqual(count, len(get_scene('unlock').diagram().beats))
            loaded = published_sections('unlock', root=destination, theme='dark')
            self.assertEqual(tuple(loaded), get_scene('unlock').diagram().beat_names())
            self.assertFalse(published_sections('unlock', root=destination, theme='light'))
            deck = select_slides(load_slides(), slide_ids=('unlock',))
            html = render_html(deck, root / 'index.html', segments={'unlock':loaded}).read_text()
            self.assertIn('published/unlock/000.mp4', html)
            self.assertIn('published/unlock/001.mp4', html)
            self.assertIn('class="scene-video"', html)
            self.assertNotIn('<video controls', html)
            meta = destination / 'unlock' / 'beats.json'
            text = meta.read_text().replace(fingerprint, 'stale')
            meta.write_text(text)
            self.assertEqual(published_sections('unlock', root=destination, theme='dark'), {})

    def test_malformed_sections_fail_without_publishing(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            index = self.build_fixture(root)
            doc = json.loads(index.read_text())
            doc[2]['video'] = '../../secret.mp4'
            index.write_text(json.dumps(doc))
            with self.assertRaisesRegex(ValueError, 'outside-root|missing'):
                _read_source_sections('unlock', index)
            self.assertFalse((root / 'published' / 'unlock').exists())

    def test_missing_index_clears_old_beat_clips_and_uses_svg_fallback(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            target = root / 'published'
            stale = target / 'clean'
            stale.mkdir(parents=True)
            (stale / 'beats.json').write_text('{}')
            count = stage_sections('clean', target=target, quality='l', theme='dark',
                                   speed=1.0, fingerprint='fake', media_dir=root)
            self.assertEqual(count, 0)
            self.assertFalse(stale.exists())


if __name__ == '__main__':
    unittest.main()
