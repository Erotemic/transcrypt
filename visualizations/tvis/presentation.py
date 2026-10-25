"""Incremental Manim video build and accompanying HTML/PDF presentation.

`all` only renders scenes with changed input geometry/renderer/icon sources.
HTML/PDF are rebuilt every time, because narration and slide layouts are
authored separately from video motion. No web server, stateful service or modification of Rust/Lean.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
from typing import Callable

from tvis.catalog import VIS_ROOT, SceneInfo, load_catalog
from tvis.gallery import build_gallery
from tvis.slide_deck import load_slides, render_html, select_slides, write_speaker_notes

MEDIA = VIS_ROOT / '.build/media'
PRESENTATION = VIS_ROOT / '.build/presentation'
MANIFEST = PRESENTATION / 'manifest.json'
COMMON_SOURCES = (
    'tvis/diagram.py',
    'tvis/plans/common.py',
    'tvis/scene_base.py',
    'tvis/components/graphics.py',
    'tvis/svg_preview.py',
    'tvis/icons.py',
    'tvis/palette.py',
    'pyproject.toml',
)
QUALITY_DIR = {'l':'480p15', 'm':'720p30', 'h':'1080p60', 'p':'1440p60'}


def scene_fingerprint(scene: SceneInfo, *, quality: str, theme: str,
                      speed: float) -> str:
    """Digest source inputs *that affect the rendered motion*, not doc notes.

    Changing a scene plan invalidates only that scene. Changes to shared
    drawing helpers or icons invalidate every clip. A narration-only TOML
    change updates the HTML without rebuilding any video clips.
    """
    hasher=hashlib.sha256(b'tvis-beat-sections-v1\0')
    inputs=[scene.file, scene.plan.replace('.','/')+'.py', *COMMON_SOURCES]
    inputs+=sorted(str(p.relative_to(VIS_ROOT))
                   for p in (VIS_ROOT/'tvis/assets/icons').glob('*.svg'))
    for rel in sorted(set(inputs)):
        hasher.update(rel.encode('utf-8') + b'\0')
        hasher.update((VIS_ROOT/rel).read_bytes())
        hasher.update(b'\0')
    hasher.update(f'{quality}|{theme}|{speed:.8g}'.encode())
    return hasher.hexdigest()


def find_manim_video(scene_id: str, quality: str) -> Path:
    """Locate a Manim output clip after a successful render command."""
    expected=MEDIA/'videos'/scene_id/QUALITY_DIR[quality]/f'{scene_id}.mp4'
    if expected.is_file():
        return expected
    choices=[p for p in (MEDIA/'videos').rglob(f'{scene_id}.mp4')
             if p.is_file() and p.parent.name == QUALITY_DIR[quality]]
    if not choices:
        raise RuntimeError(f'Manim returned success but no {QUALITY_DIR[quality]} '
                           f'MP4 was found for {scene_id} under {MEDIA}')
    return max(choices,key=lambda path:path.stat().st_mtime_ns)


def publish_scene(scene_id: str, *, quality: str='l', theme: str='dark',
                  speed: float=1.0, force: bool=False,
                  render_scene: Callable[[str], Path]) -> tuple[Path, bool]:
    """Render or reuse one complete scene and make it available to HTML export.

    The manifest shared with `all` avoids rendering this scene a second time.
    Partial animations and stills must not be published as complete clips.
    """
    if quality not in QUALITY_DIR or theme not in {'dark', 'light'} or not 0.1 <= speed <= 10:
        raise ValueError('invalid quality, theme or speed')
    from tvis.catalog import get_scene
    scene = get_scene(scene_id)
    fingerprint = scene_fingerprint(scene, quality=quality, theme=theme, speed=speed)
    old = {}
    if MANIFEST.is_file():
        try:
            doc = json.loads(MANIFEST.read_text(encoding='utf-8'))
            if doc.get('format') == 1:
                old = doc.get('clips', {})
        except (OSError, ValueError, TypeError):
            pass
    destination = PRESENTATION / 'videos' / f'{scene_id}.mp4'
    if not force and old.get(scene_id) == fingerprint and destination.is_file() and destination.stat().st_size:
        return destination, False
    source = Path(render_scene(scene_id))
    if not source.is_file() or source.stat().st_size <= 0:
        raise RuntimeError(f'empty or missing rendered video for {scene_id}: {source}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix('.mp4.part')
    shutil.copyfile(source, temporary)
    os.replace(temporary, destination)
    from tvis.beat_media import stage_sections
    stage_sections(scene_id, target=PRESENTATION / 'videos' / 'sections',
                   quality=quality, theme=theme, speed=speed,
                   fingerprint=fingerprint, media_dir=MEDIA)
    old[scene_id] = fingerprint
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    tmp = MANIFEST.with_suffix('.json.part')
    tmp.write_text(json.dumps({'format': 1, 'clips': old}, indent=2) + '\n', encoding='utf-8')
    os.replace(tmp, MANIFEST)
    return destination, True


def build_presentation(*, quality: str='l', theme: str='dark', speed: float=1.0,
                       force: bool=False, render_scene: Callable[[str], Path],
                       formats: str='both', embed_videos: bool=False) -> tuple[Path, tuple[str,...]]:
    """Build changed video scenes and refresh HTML; return path and scene IDs.

    ``render_scene`` executes a real Manim render in the CLI; injected test
    renderers are supported to exercise cache policy without installing Manim.
    Failed renders do not change the cached build manifest or replace the video.
    """
    if quality not in QUALITY_DIR or theme not in {'dark','light'} or not 0.1 <= speed <= 10:
        raise ValueError('invalid quality, theme or speed')
    _deck, scenes=load_catalog()
    old={}
    if MANIFEST.exists():
        try:
            doc=json.loads(MANIFEST.read_text())
            if doc.get('format') == 1:
                old=doc.get('clips',{})
        except (OSError,ValueError,TypeError):
            old={}
    videos=PRESENTATION/'videos'
    videos.mkdir(parents=True,exist_ok=True)
    new={}; rendered=[]
    for scene in scenes:
        destination=videos/f'{scene.id}.mp4'
        fingerprint=scene_fingerprint(scene,quality=quality,theme=theme,speed=speed)
        if force or old.get(scene.id) != fingerprint or not destination.is_file():
            source=Path(render_scene(scene.id))
            if not source.is_file() or source.stat().st_size <= 0:
                raise RuntimeError(f'empty or missing rendered video for {scene.id}: {source}')
            # Copy atomically to keep a valid previous clip if interrupted.
            temporary=destination.with_suffix('.mp4.part')
            shutil.copyfile(source,temporary)
            os.replace(temporary,destination)
            from tvis.beat_media import stage_sections
            stage_sections(scene.id, target=videos / 'sections',
                           quality=quality, theme=theme, speed=speed,
                           fingerprint=fingerprint, media_dir=MEDIA)
            rendered.append(scene.id)
        new[scene.id]=fingerprint
    # Presentation and source inspector always regenerate; narration and
    # slide layout edits do not invalidate expensive Manim media renders.
    outputs = export_presentation(theme=theme, formats=formats, embed_videos=embed_videos)
    output=outputs.get('html', outputs.get('pdf'))
    tmp=MANIFEST.with_suffix('.json.part')
    tmp.write_text(json.dumps({'format':1,'clips':new},indent=2)+'\n')
    os.replace(tmp,MANIFEST)
    return output, tuple(rendered)


def export_presentation(*, theme: str='dark', formats: str='both',
                        embed_videos: bool=False,
                        scene_ids: tuple[str, ...]=(),
                        slide_ids: tuple[str, ...]=()) -> dict[str, Path]:
    """Export slides with no Manim render, optionally selecting scenes/slides.

    A filtered deck gets independent filenames, preserving the full deck.
    PDF-only means precisely PDF: no HTML, inspector, or gallery regeneration.
    Existing videos may decorate HTML, but PDF works without them.
    """
    if formats not in {'both', 'html', 'pdf'}:
        raise ValueError('formats must be html, pdf, or both')
    if embed_videos and formats == 'pdf':
        raise ValueError('--embed-videos requires HTML output')
    deck = select_slides(load_slides(), scene_ids=scene_ids, slide_ids=slide_ids)
    PRESENTATION.mkdir(parents=True, exist_ok=True)
    keys = tuple(scene_ids or slide_ids)
    if keys:
        label = '-'.join(keys)
        if len(label) > 70:
            label = 'selection-' + hashlib.sha256(label.encode()).hexdigest()[:12]
        suffix = '-' + label
    else:
        suffix = ''
    html_target = PRESENTATION / f'index{suffix}.html'
    clips = {s.scene.id: PRESENTATION / 'videos' / f'{s.scene.id}.mp4'
             for s in deck.slides}
    clips = {k: v for k, v in clips.items() if v.is_file() and v.stat().st_size}
    written = {}
    if formats in {'both', 'html'}:
        from tvis.beat_media import published_sections
        segments = {s.scene.id: published_sections(
            s.scene.id, root=PRESENTATION / 'videos' / 'sections', theme=theme)
            for s in deck.slides}
        segments = {k: v for k, v in segments.items() if v}
        written['html'] = render_html(deck, html_target, theme=theme, segments=segments)
        if embed_videos:
            written['embedded'] = render_html(
                deck, PRESENTATION / f'embedded{suffix}.html',
                theme=theme, segments=segments, embed_videos=True)
    if formats in {'both', 'pdf'}:
        from tvis.pdf_slides import render_pdf
        # A PDF-only build should not claim playable video if its companion
        # HTML is not present. Exporting both creates the companion above.
        linked = set(clips) if html_target.is_file() else set()
        written['pdf'] = render_pdf(
            deck, PRESENTATION / f'presentation{suffix}.pdf',
            theme=theme, video_scenes=linked, html_name=html_target.name)
    if formats == 'both':
        written['notes'] = write_speaker_notes(
            deck, PRESENTATION / f'speaker-notes{suffix}.md')
        if not keys:
            # The detailed inspector is expensive and describes ALL scenes.
            # Only the explicit full-deck build needs to refresh it.
            written['inspector'] = build_gallery(
                PRESENTATION / 'storyboard.html', theme=theme,
                videos={k: f'videos/{k}.mp4' for k in clips})
    return written
