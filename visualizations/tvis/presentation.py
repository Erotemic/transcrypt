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
from tvis.slide_deck import load_slides, render_html, write_speaker_notes

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
    hasher=hashlib.sha256()
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
                        embed_videos: bool=False) -> dict[str, Path]:
    """Export heterogeneous slides without requiring Manim to be installed.

    Existing clips under ``.build/presentation/videos`` are used whenever
    present. Missing clips degrade to their plan-derived static diagram beat.
    PDF pages show stills with an HTML playback link, rather than pretending
    MP4s play in arbitrary PDF viewers.
    """
    if formats not in {'both','html','pdf'}:
        raise ValueError('formats must be html, pdf, or both')
    if embed_videos and formats == 'pdf':
        raise ValueError('--embed-videos requires HTML output')
    deck=load_slides()
    PRESENTATION.mkdir(parents=True,exist_ok=True)
    clips={s.scene.id: PRESENTATION/'videos'/f'{s.scene.id}.mp4' for s in deck.slides}
    clips={k:v for k,v in clips.items() if v.is_file() and v.stat().st_size}
    written={}
    if formats in {'both','html'}:
        written['html']=render_html(deck,PRESENTATION/'index.html',theme=theme,videos=clips)
        if embed_videos:
            written['embedded']=render_html(deck,PRESENTATION/'embedded.html',
                                            theme=theme,videos=clips,embed_videos=True)
    if formats in {'both','pdf'}:
        from tvis.pdf_slides import render_pdf
        written['pdf']=render_pdf(deck,PRESENTATION/'presentation.pdf',
                                  theme=theme,video_scenes=set(clips))
    written['notes']=write_speaker_notes(deck,PRESENTATION/'speaker-notes.md')
    # The inspector remains a distinct, more technical artifact. Unlike the
    # presentation, it allows scrubbing every beat and viewing all source refs.
    written['inspector']=build_gallery(PRESENTATION/'storyboard.html',theme=theme,
                                       videos={k:f'videos/{k}.mp4' for k in clips})
    return written
