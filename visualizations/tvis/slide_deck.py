"""Heterogeneous 16:9 presentation from the same editable, evidence-checked plans.

The scene storyboard describes facts and time. ``presentation.toml`` controls
actual slide boundaries and layouts. Neither HTML nor PDF upgrades a proof
claim; every operation badge is read directly from the shared scene plan.
"""
from __future__ import annotations

import base64
from dataclasses import dataclass
from html import escape
import json
from pathlib import Path
import tomllib
from typing import Mapping

from tvis.catalog import VIS_ROOT, SceneInfo, get_scene
from tvis.diagram import EVIDENCE_LABELS
from tvis.palette import palette
from tvis.svg_preview import render_svg

SLIDES_FILE = VIS_ROOT / 'storyboards/presentation.toml'
LAYOUTS = frozenset({'cover', 'cinema', 'split', 'diagram', 'evidence', 'statement'})


@dataclass(frozen=True)
class Slide:
    id: str
    layout: str
    title: str
    scene: SceneInfo
    kicker: str = ''
    subtitle: str = ''
    beat: str = 'last'
    media: str = 'diagram'
    points: tuple[str, ...] = ()

    @property
    def diagram(self):
        return self.scene.diagram()

    @property
    def active_operation(self) -> str | None:
        beat = self.diagram.state(self.beat)[2]
        return beat.processing.node if beat.processing else None


@dataclass(frozen=True)
class SlideDeck:
    title: str
    subtitle: str
    footer: str
    slides: tuple[Slide, ...]


def load_slides(path: Path = SLIDES_FILE) -> SlideDeck:
    doc = tomllib.loads(path.read_text(encoding='utf-8'))
    metadata = doc.get('deck', {})
    if not isinstance(metadata.get('title'), str) or not metadata['title'].strip():
        raise ValueError('presentation deck needs a title')
    slides = []
    seen = set()
    for i, item in enumerate(doc.get('slide', ()), start=1):
        slide_id = item.get('id', '')
        layout = item.get('layout', '')
        if not isinstance(slide_id, str) or not slide_id or slide_id in seen:
            raise ValueError(f'slide {i}: missing or duplicate id {slide_id!r}')
        seen.add(slide_id)
        if layout not in LAYOUTS:
            raise ValueError(f'slide {slide_id}: unknown layout {layout!r}')
        scene = get_scene(item.get('scene', ''))
        beat = item.get('beat', 'last')
        if not isinstance(beat, str):
            raise ValueError(f'slide {slide_id}: beat must be a named beat or last')
        try:
            scene.diagram().state(beat)
        except ValueError as exc:
            raise ValueError(f'slide {slide_id}: {exc}') from exc
        media = item.get('media', 'video' if layout in {'cinema', 'split'} else 'diagram')
        if media not in {'video', 'diagram'}:
            raise ValueError(f'slide {slide_id}: media must be diagram or video')
        if not isinstance(item.get('title'), str) or not item['title'].strip():
            raise ValueError(f'slide {slide_id}: title is required')
        points = item.get('points', [])
        if not isinstance(points, list) or any(not isinstance(p, str) for p in points):
            raise ValueError(f'slide {slide_id}: points must be a list of strings')
        slides.append(Slide(slide_id, layout, item['title'], scene,
                            item.get('kicker', ''), item.get('subtitle', ''), beat,
                            media, tuple(points)))
    if not slides:
        raise ValueError('presentation requires at least one slide')
    return SlideDeck(metadata['title'], metadata.get('subtitle', ''),
                     metadata.get('footer', ''), tuple(slides))


def _svg_url(slide: Slide, theme: str) -> str:
    picture = render_svg(slide.diagram, beat=slide.beat, theme=theme).encode('utf-8')
    return 'data:image/svg+xml;base64,' + base64.b64encode(picture).decode('ascii')


def _operations(slide: Slide, limit: int = 6) -> str:
    nodes = [n for n in slide.diagram.nodes if n.evidence]
    if not nodes:
        return '<p class="quiet">No operation badges on this scene; consult the associated sources.</p>'
    cards = []
    for node in nodes[:limit]:
        ev = node.evidence
        active = ' active-operation' if node.key == slide.active_operation else ''
        cards.append(
            f'<div class="op-card tier-{ev.level}{active}">'
            f'<div class="op-title">{escape(node.title)}</div>'
            f'<div class="op-tier">{escape(EVIDENCE_LABELS[ev.level])}</div>'
            f'<div class="op-basis">{escape(ev.basis)} · {escape(ev.note)}</div></div>'
        )
    if len(nodes) > limit:
        cards.append(f'<p class="quiet">+{len(nodes)-limit} more operations in the storyboard inspector</p>')
    return ''.join(cards)


def _visual(slide: Slide, poster: str, video_scenes: set[str]) -> str:
    scene = escape(slide.scene.id)
    still = f'<img class="diagram-picture" src="{poster}" alt="{escape(slide.diagram.title)}: {escape(slide.beat)}">'
    if slide.media == 'video' and slide.scene.id in video_scenes:
        # The video URL is injected lazily on slide activation, not loaded all at once.
        return (f'<video class="scene-video" data-scene="{scene}" poster="{poster}" '
                f'controls playsinline preload="none" aria-label="Manim animation: {escape(slide.title)}">'
                'Your browser does not support embedded MP4 video.</video>')
    if slide.media == 'video':
        return still + '<span class="fallback-note">Static beat · render Manim to enable motion</span>'
    return still


def _slide_html(slide: Slide, index: int, total: int, theme: str,
                video_scenes: set[str]) -> str:
    poster = _svg_url(slide, theme)
    picture = _visual(slide, poster, video_scenes)
    bullets = ''.join(f'<li>{escape(p)}</li>' for p in slide.points)
    sub = f'<p class="subtitle">{escape(slide.subtitle)}</p>' if slide.subtitle else ''
    title = (f'<div class="slide-heading"><div class="eyebrow">{escape(slide.kicker)}</div>'
             f'<h2>{escape(slide.title)}</h2>{sub}</div>')
    ops = _operations(slide)
    if slide.layout == 'cover':
        body = (f'<div class="cover-body"><div class="cover-copy">{title}'
                f'<ul class="points">{bullets}</ul><div class="accent-line"></div></div>'
                f'<div class="cover-art">{picture}</div></div>')
    elif slide.layout == 'cinema':
        body = (f'{title}<div class="cinema-body"><div class="visual">{picture}</div>'
                f'<div class="cinema-caption"><ul class="points">{bullets}</ul></div></div>')
    elif slide.layout == 'split':
        body = (f'{title}<div class="split-body"><div class="visual">{picture}</div>'
                f'<div class="split-aside"><ul class="points">{bullets}</ul>'
                f'<div class="mini-evidence"><h3>Evidence per operation</h3>{ops}</div></div></div>')
    elif slide.layout == 'diagram':
        body = (f'{title}<div class="diagram-body"><div class="visual">{picture}</div>'
                f'<div class="diagram-caption">{escape("   /   ".join(slide.points))}</div></div>')
    elif slide.layout == 'evidence':
        body = (f'{title}<div class="evidence-body"><div class="operation-grid">{ops}</div>'
                f'<ul class="points">{bullets}</ul></div>')
    else:
        body = (f'<div class="statement-body">{title}<ul class="points">{bullets}</ul>'
                f'<div class="statement-rail"><span>DATA</span><span>PROOF</span>'
                f'<span>DEPENDENCIES</span></div></div>')
    return (f'<section class="slide layout-{slide.layout}" id="slide-{escape(slide.id)}"'
            f' data-slide-id="{escape(slide.id)}" data-scene="{escape(slide.scene.id)}" '
            f'aria-label="Slide {index}: {escape(slide.title)}" hidden>'
            f'{body}<footer class="slide-footer"><span>Scene: {escape(slide.scene.id)} · Evidence applies per operation</span>'
            f'<span>{index:02d} / {total:02d}</span></footer></section>')


def render_html(deck: SlideDeck, target: Path, *, theme: str = 'dark',
                videos: Mapping[str, Path] | None = None, embed_videos: bool = False) -> Path:
    """Presentation HTML with heterogeneous slide layouts and actual video tags.

    ``embed_videos=True`` base64-inlines MP4s once per scene, yielding a single
    distributable HTML file. The default uses relative MP4 sidecars to avoid a
    huge HTML. A scene with no video receives a faithful SVG still, not fake motion.
    """
    palette(theme)  # Reject an invalid theme before writing an artifact.
    videos = videos or {}
    video_urls = {}
    for scene, path in videos.items():
        source = Path(path)
        if not source.is_file() or not source.stat().st_size:
            continue
        if embed_videos:
            video_urls[scene] = ('data:video/mp4;base64,' +
                                 base64.b64encode(source.read_bytes()).decode('ascii'))
        else:
            # Relative paths also work when the entire directory is moved.
            video_urls[scene] = source.relative_to(target.parent).as_posix() if source.is_relative_to(target.parent) else source.name
    sections = '\n'.join(_slide_html(slide, i, len(deck.slides), theme, set(video_urls))
                         for i, slide in enumerate(deck.slides, start=1))
    video_json = json.dumps(video_urls, ensure_ascii=True).replace('<', '\\u003c')
    notes_json = json.dumps({s.id: {'narration': s.scene.narration,
                                    'sources': list(s.scene.sources),
                                    'proofs': list(s.scene.proof_anchors)}
                             for s in deck.slides}, ensure_ascii=True).replace('<', '\\u003c')
    css = (VIS_ROOT / 'tvis/assets/presentation.css').read_text(encoding='utf-8')
    js = (VIS_ROOT / 'tvis/assets/presentation.js').read_text(encoding='utf-8')
    html = (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{escape(deck.title)}</title><style>{css}</style></head>'
            f'<body data-theme="{theme}"><header class="presenter-bar">'
            f'<div class="presenter-name">TRANSCRYPT <span>V3</span> / TRUST AT EVERY OPERATION</div>'
            f'<div class="presenter-controls"><button id="prev" type="button" aria-label="Previous slide">‹</button>'
            f'<span id="counter" aria-live="polite"></span>'
            f'<button id="next" type="button" aria-label="Next slide">›</button>'
            f'<button id="notes-button" type="button" title="Speaker notes (N)">Notes</button>'
            f'<button id="fullscreen" type="button" title="Fullscreen (F)">Fullscreen</button></div></header>'
            f'<main class="presentation" id="presentation">{sections}</main>'
            f'<div class="progress" aria-hidden="true"><div id="progress-bar"></div></div>'
            f'<aside class="notes-panel" id="notes-panel" hidden><h3>Presenter notes · <span id="notes-title"></span></h3>'
            f'<p id="notes-text"></p><p class="notes-sources" id="notes-sources"></p></aside>'
            f'<p class="shortcut-hint">← / → navigate · Space play/pause · N notes · F fullscreen</p>'
            f'<script type="application/json" id="video-data">{video_json}</script>'
            f'<script type="application/json" id="notes-data">{notes_json}</script>'
            f'<script>{js}</script></body></html>')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(html, encoding='utf-8')
    return target


def write_speaker_notes(deck: SlideDeck, target: Path) -> Path:
    """Companion transcript, with source references and exact proof anchors."""
    lines = [f'# {deck.title}', '', deck.subtitle, '',
             'Presenter transcript. Proof names are scoped to their source; do not treat external premises as proved.', '']
    for i, s in enumerate(deck.slides, 1):
        lines.extend([f'## {i:02d}. {s.title}', '', f'*Slide layout: {s.layout}; source scene: `{s.scene.id}`*', '',
                      s.scene.narration, ''])
        if s.points:
            lines.extend(['On-screen points:', ''] + [f'- {p}' for p in s.points] + [''])
        if s.scene.proof_anchors:
            lines.extend(['Lean anchors: ' + ', '.join(f'`{x}`' for x in s.scene.proof_anchors), ''])
        lines.extend(['Source files:', ''] + [f'- `{src}`' for src in s.scene.sources] + [''])
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text('\n'.join(lines) + '\n', encoding='utf-8')
    return target
