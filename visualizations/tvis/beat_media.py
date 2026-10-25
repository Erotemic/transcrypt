"""Publish Manim ``next_section`` clips for click-to-advance HTML beats.

A diagram scene calls ``next_section(beat.key)`` once per beat. Rendering with
``--save_sections`` produces a JSON index and one MP4 per section. The HTML
presentation plays one section on each advance and stops at its final frame.

No Manim import is necessary to read these files or render a static deck.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import tempfile
from typing import Mapping

from tvis.catalog import get_scene


def _source_index(scene_id: str, quality: str, media_dir: Path) -> Path:
    from tvis.presentation import QUALITY_DIR
    return (media_dir / 'videos' / scene_id / QUALITY_DIR[quality] / 'sections'
            / f'{scene_id}.json')


def _read_source_sections(scene_id: str, index: Path) -> tuple[tuple[str, Path], ...]:
    """Require one valid video for *every* authored beat, in authored order.

    Manim adds a leading auto-created title section; it is intentionally not
    one of the click-through beats. Other unmatched sections are an error.
    Paths from Manim's JSON index are untrusted inputs, so keep them contained.
    """
    beat_names = tuple(beat.key for beat in get_scene(scene_id).diagram().beats)
    doc = json.loads(index.read_text(encoding='utf-8'))
    if not isinstance(doc, list):
        raise ValueError(f'{index}: expected Manim section list')
    sequence = []
    root = index.parent.resolve()
    for entry in doc:
        if not isinstance(entry, dict):
            raise ValueError(f'{index}: non-object section')
        name = entry.get('name')
        if name in {'autocreated', 'unnamed'} and not sequence:
            continue
        if name not in beat_names:
            raise ValueError(f'{index}: unexpected section {name!r}')
        filename = entry.get('video')
        if not isinstance(filename, str) or not filename.endswith('.mp4'):
            raise ValueError(f'{index}: missing MP4 for beat {name!r}')
        path = (root / filename).resolve()
        if not path.is_relative_to(root) or not path.is_file() or path.stat().st_size <= 0:
            raise ValueError(f'{index}: missing or outside-root MP4 for {name!r}: {filename}')
        sequence.append((name, path))
    if tuple(name for name, _ in sequence) != beat_names:
        raise ValueError(f'{scene_id}: Manim sections do not match authored beats: '
                         f'{[name for name, _ in sequence]!r} != {beat_names!r}')
    return tuple(sequence)


def stage_sections(scene_id: str, *, target: Path, quality: str, theme: str,
                   speed: float, fingerprint: str, media_dir: Path,
                   section_index: Path | None = None) -> int:
    """Stage all beats atomically, or remove obsolete media and use SVG fallback.

    Missing section output is allowed for test renderers and pre-section clips.
    An existing but malformed Manim index is *not* silently accepted.
    """
    source = section_index or _source_index(scene_id, quality, media_dir)
    directory = target / scene_id
    if not source.is_file():
        if directory.exists():
            shutil.rmtree(directory)
        return 0
    clips = _read_source_sections(scene_id, source)
    target.mkdir(parents=True, exist_ok=True)
    temp = Path(tempfile.mkdtemp(prefix=f'.{scene_id}-', dir=target))
    backup = target / f'.{scene_id}-previous'
    try:
        entries = []
        for index, (name, path) in enumerate(clips):
            # Numerical names avoid putting authored/untrusted text into paths.
            filename = f'{index:03d}.mp4'
            shutil.copyfile(path, temp / filename)
            entries.append({'name': name, 'file': filename})
        (temp / 'beats.json').write_text(
            json.dumps({'format': 1, 'quality': quality, 'theme': theme,
                        'speed': speed, 'fingerprint': fingerprint,
                        'beats': entries}, indent=2) + '\n', encoding='utf-8')
        if backup.exists():
            shutil.rmtree(backup)
        if directory.exists():
            directory.rename(backup)
        try:
            os.replace(temp, directory)
        except OSError:
            if backup.exists() and not directory.exists():
                os.replace(backup, directory)
            raise
        if backup.exists():
            shutil.rmtree(backup)
    finally:
        if temp.exists():
            shutil.rmtree(temp)
    return len(clips)


def published_sections(scene_id: str, *, root: Path, theme: str) -> Mapping[str, Path]:
    """Return current staged sections; never show stale or mismatched animations."""
    from tvis.presentation import scene_fingerprint
    directory = root / scene_id
    meta = directory / 'beats.json'
    if not meta.is_file():
        return {}
    try:
        document = json.loads(meta.read_text(encoding='utf-8'))
        if (document.get('format') != 1 or document.get('theme') != theme
                or not isinstance(document.get('beats'), list)):
            return {}
        quality, speed = document['quality'], document['speed']
        if document['fingerprint'] != scene_fingerprint(
                get_scene(scene_id), quality=quality, theme=theme, speed=speed):
            return {}
        expected = tuple(beat.key for beat in get_scene(scene_id).diagram().beats)
        result = {}
        for record in document['beats']:
            name, filename = record['name'], record['file']
            path = (directory / filename).resolve()
            if (not path.is_relative_to(directory.resolve()) or not path.is_file()
                    or path.stat().st_size <= 0 or name in result):
                return {}
            result[name] = path
        if tuple(result) != expected:
            return {}
        return result
    except (OSError, ValueError, TypeError, KeyError):
        return {}
