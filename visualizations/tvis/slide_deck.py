"""Heterogeneous 16:9 presentation from the same editable, evidence-checked plans.

The scene storyboard describes facts and time. ``presentation.toml`` controls
actual slide boundaries and layouts. Neither HTML nor PDF upgrades a proof
claim; every operation badge is read directly from the shared scene plan.
"""
from __future__ import annotations

import base64
from dataclasses import dataclass, replace
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
    steps: str = 'single'  # 'all' -> click through every planned beat

    @property
    def diagram(self):
        return self.scene.diagram()

    @property
    def beat_names(self) -> tuple[str, ...]:
        if self.steps == 'all':
            return self.diagram.beat_names()
        return (self.beat,)

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
        steps = item.get('steps', 'all' if media == 'video' else 'single')
        if steps not in {'all', 'single'}:
            raise ValueError(f'slide {slide_id}: steps must be all or single')
        points = item.get('points', [])
        if not isinstance(points, list) or any(not isinstance(p, str) for p in points):
            raise ValueError(f'slide {slide_id}: points must be a list of strings')
        slides.append(Slide(slide_id, layout, item['title'], scene,
                            item.get('kicker', ''), item.get('subtitle', ''), beat,
                            media, tuple(points), steps))
    if not slides:
        raise ValueError('presentation requires at least one slide')
    return SlideDeck(metadata['title'], metadata.get('subtitle', ''),
                     metadata.get('footer', ''), tuple(slides))


def select_slides(deck: SlideDeck, *, scene_ids: tuple[str, ...]=(),
                  slide_ids: tuple[str, ...]=()) -> SlideDeck:
    """Return a focused deck without changing the authored order or layouts."""
    if scene_ids and slide_ids:
        raise ValueError('select either scenes or slides, not both')
    if not scene_ids and not slide_ids:
        return deck
    if scene_ids:
        from tvis.catalog import get_scene
        for scene_id in scene_ids:
            get_scene(scene_id)  # Reject typos rather than generating an empty PDF.
        wanted = set(scene_ids)
        selected = tuple(slide for slide in deck.slides if slide.scene.id in wanted)
    else:
        available = {slide.id for slide in deck.slides}
        missing = set(slide_ids) - available
        if missing:
            raise ValueError('unknown slide(s): ' + ', '.join(sorted(missing)))
        wanted = set(slide_ids)
        selected = tuple(slide for slide in deck.slides if slide.id in wanted)
    if not selected:
        raise ValueError('selection contains no presentation slides')
    return replace(deck, slides=selected)


def _svg_url(slide: Slide, theme: str, beat: str | None = None) -> str:
    picture = render_svg(slide.diagram, beat=beat or slide.beat, theme=theme).encode('utf-8')
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
            f'<div class="op-card tier-{ev.level}{active}" data-op-node="{escape(node.key)}">'
            f'<div class="op-title">{escape(node.title)}</div>'
            f'<div class="op-tier">{escape(EVIDENCE_LABELS[ev.level])}</div>'
            f'<div class="op-basis">{escape(ev.basis)} · {escape(ev.note)}</div></div>'
        )
    if len(nodes) > limit:
        cards.append(f'<p class="quiet">+{len(nodes)-limit} more operations in the storyboard inspector</p>')
    return ''.join(cards)


def _visual(slide: Slide, poster: str, video_scenes: set[str]) -> str:
    """Present still snapshots or auto-play one self-contained Manim beat.

    A scene's monolithic MP4 is intentionally never offered as an HTML player.
    Each click advances one beat (matching the DKPS manim-slides interaction).
    Without section clips, the same clicks show exact plan-derived SVG states.
    """
    still = (f'<img class="diagram-picture" src="{poster}" '
             f'alt="{escape(slide.diagram.title)}: {escape(slide.beat)}">')
    video = ('<video class="scene-video" muted playsinline preload="none" hidden '
             f'aria-label="Current animation beat of {escape(slide.title)}"></video>')
    note = ('<span class="fallback-note">SVG beat snapshots · render scene for motion</span>'
            if slide.media == 'video' and slide.steps == 'all'
            and slide.scene.id not in video_scenes else '')
    return f'<div class="visual-media">{still}{video}{note}</div>'


def _slide_html(slide: Slide, index: int, total: int, theme: str,
                video_scenes: set[str], poster: str) -> str:
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
    beat_bar = ''
    if len(slide.beat_names) > 1:
        beat_bar = ('<div class="beat-tracker" aria-live="polite">'
                    '<span class="beat-number" data-role="beat-number"></span>'
                    '<span class="beat-caption" data-role="beat-caption"></span>'
                    '<span class="beat-tier" data-role="beat-tier"></span>'
                    '</div>')
    return (f'<section class="slide layout-{slide.layout}" id="slide-{escape(slide.id)}"'
            f' data-slide-id="{escape(slide.id)}" data-scene="{escape(slide.scene.id)}" '
            f' data-media="{escape(slide.media)}" '
            f'aria-label="Slide {index}: {escape(slide.title)}" hidden>'
            f'{body}{beat_bar}<footer class="slide-footer"><span>Scene: {escape(slide.scene.id)} · Evidence applies per operation</span>'
            f'<span>{index:02d} / {total:02d}</span></footer></section>')


def _beat_status_label(status: str) -> str:
    return {
        'explainer': 'EXPLANATION', 'implemented': 'IN CODE: NO PROOF',
        'proved': 'SOURCE-DERIVED PROOF', 'modeled': 'LEAN MODEL',
        'tested': 'RUNTIME TESTED', 'assumed': 'TRUSTED EXTERNAL',
        'planned': 'DESIGN GOAL', 'open': 'NOT YET PROVED',
    }[status]


def _state_payload(slide: Slide, theme: str, image_cache: dict) -> list[dict]:
    plan = slide.diagram
    operations = plan.node_map()
    result = []
    for name in slide.beat_names:
        _nodes, _links, stage, _index = plan.state(name)
        active = stage.processing.node if stage.processing else None
        node = operations.get(active) if active else None
        evidence = node.evidence if node else None
        key = (slide.scene.id, name)
        if key not in image_cache:
            image_cache[key] = _svg_url(slide, theme, name)
        flow = ''
        if stage.processing:
            flow = f'{stage.processing.before} → {stage.processing.after}'
        elif stage.packet:
            link = plan.link_map()[stage.packet]
            flow = (f'{operations[link.origin].title} → '
                    f'{stage.packet_label or link.label} → {operations[link.destination].title}')
        result.append({
            'name': name, 'caption': stage.caption,
            'poster': image_cache[key], 'status': stage.status,
            'flow': flow, 'active': active,
            'tier': (evidence.level if evidence else ''),
            'evidence': (EVIDENCE_LABELS[evidence.level] if evidence
                         else _beat_status_label(stage.status)),
        })
    return result


def render_html(deck: SlideDeck, target: Path, *, theme: str = 'dark',
                segments: Mapping[str, Mapping[str, Path]] | None = None,
                embed_videos: bool = False) -> Path:
    """Export a click-through HTML deck; no full-scene movie controls.

    Manim sections, when available, automatically play one beat and freeze at
    its final frame. No staged media? Each click swaps in the exact SVG state.
    ``embed_videos`` inlines each *beat* MP4 once, for offline portability.
    """
    palette(theme)
    segments = segments or {}
    clip_urls = {}
    for scene, beats in segments.items():
        scene_urls = {}
        for beat, path in beats.items():
            source = Path(path)
            if not source.is_file() or not source.stat().st_size:
                continue
            if embed_videos:
                url = ('data:video/mp4;base64,'
                       + base64.b64encode(source.read_bytes()).decode('ascii'))
            elif source.is_relative_to(target.parent):
                url = source.relative_to(target.parent).as_posix()
            else:
                url = source.name
            scene_urls[beat] = url
        if scene_urls:
            clip_urls[scene] = scene_urls
    image_cache = {}
    step_map = {s.id: _state_payload(s, theme, image_cache) for s in deck.slides}
    sections = '\n'.join(
        _slide_html(slide, i, len(deck.slides), theme, set(clip_urls),
                    step_map[slide.id][0]['poster'])
        for i, slide in enumerate(deck.slides, start=1))
    def as_json(value) -> str:
        return json.dumps(value, ensure_ascii=True).replace('<', '\\u003c')
    steps_json = as_json(step_map)
    video_json = as_json(clip_urls)
    notes_json = as_json({s.id: {'narration': s.scene.narration,
                                 'sources': list(s.scene.sources),
                                 'proofs': list(s.scene.proof_anchors)}
                          for s in deck.slides})
    css = (VIS_ROOT / 'tvis/assets/presentation.css').read_text(encoding='utf-8')
    js = (VIS_ROOT / 'tvis/assets/presentation.js').read_text(encoding='utf-8')
    html = (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{escape(deck.title)}</title><style>{css}</style></head>'
            f'<body data-theme="{theme}"><header class="presenter-bar">'
            f'<div class="presenter-name">TRANSCRYPT <span>V3</span> / TRUST AT EVERY OPERATION</div>'
            f'<div class="presenter-controls">'
            f'<button id="prev-slide" type="button" title="Previous slide (Shift+Left)" '
            f'aria-label="Previous slide">«</button>'
            f'<button id="prev" type="button" title="Previous beat (Left)" '
            f'aria-label="Previous beat">‹</button>'
            f'<span id="counter" aria-live="polite"></span>'
            f'<button id="next" type="button" title="Next beat (Right or click)" '
            f'aria-label="Next beat">›</button>'
            f'<button id="next-slide" type="button" title="Next slide (Shift+Right)" '
            f'aria-label="Next slide">»</button>'
            f'<button id="notes-button" type="button" title="Speaker notes (N)">Notes</button>'
            f'<button id="fullscreen" type="button" title="Fullscreen (F)">Fullscreen</button>'
            f'</div></header>'
            f'<main class="presentation" id="presentation">{sections}</main>'
            f'<div class="progress" aria-hidden="true"><div id="progress-bar"></div></div>'
            f'<aside class="notes-panel" id="notes-panel" hidden><h3>Presenter notes · <span id="notes-title"></span></h3>'
            f'<p id="notes-text"></p><p class="notes-sources" id="notes-sources"></p></aside>'
            f'<p class="shortcut-hint">Click / → / Space: next beat · ← back · Shift+←/→: slide · R: replay beat · N notes</p>'
            f'<script type="application/json" id="step-data">{steps_json}</script>'
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
