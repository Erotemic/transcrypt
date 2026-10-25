"""Incremental Manim video build and accompanying local HTML presentation.

`all` only renders scenes with changed input geometry/renderer/icon sources.
The HTML is rebuilt every time, because narration is authored separately from
video motion. No web server, stateful service or modification of Rust/Lean.
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

MEDIA = VIS_ROOT / '.build/media'
PRESENTATION = VIS_ROOT / '.build/presentation'
MANIFEST = PRESENTATION / 'manifest.json'
COMMON_SOURCES = (
    'tvis/diagram.py',
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
                       force: bool=False, render_scene: Callable[[str], Path]) -> tuple[Path, tuple[str,...]]:
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
    # HTML always regenerates: claim/narration/scene order may have changed.
    output=PRESENTATION/'index.html'
    build_gallery(output,theme=theme,
                  videos={s.id:f'videos/{s.id}.mp4' for s in scenes})
    tmp=MANIFEST.with_suffix('.json.part')
    tmp.write_text(json.dumps({'format':1,'clips':new},indent=2)+'\n')
    os.replace(tmp,MANIFEST)
    return output, tuple(rendered)
