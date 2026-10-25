"""Single offline vector-icon source used by both SVG and Manim.

Icons are local fixed SVG files, not downloaded while rendering. The program
never loads SVG paths from storyboard prose or guest/provider data.
"""
from __future__ import annotations

from functools import lru_cache
from pathlib import Path
from xml.etree import ElementTree as ET

ICON_DIR = Path(__file__).resolve().parent / 'assets/icons'
NAMES = frozenset({
    'document', 'laptop', 'filter', 'key', 'cloud', 'shield',
    'git', 'code', 'proof', 'warning', 'path', 'config',
    'lock', 'vault', 'database',
})
ROLE_ICONS = {
    'guest': 'laptop', 'broker': 'filter', 'provider': 'cloud',
    'policy': 'path', 'secret': 'vault', 'neutral': 'document',
    'proved': 'proof', 'assumed': 'warning', 'open': 'warning',
}


def icon_name(node) -> str:
    name = node.icon or ROLE_ICONS.get(node.role, 'document')
    if name not in NAMES:
        raise ValueError(f'unknown icon {name!r} for node {node.key}')
    return name


def icon_path(name: str) -> Path:
    if name not in NAMES:
        raise ValueError(f'unknown icon {name!r}')
    return ICON_DIR / f'{name}.svg'


@lru_cache(maxsize=None)
def icon_art(name: str) -> tuple[bool, tuple[tuple[str, tuple[tuple[str, str], ...]], ...]]:
    """Return vetted SVG primitives; avoid embedding raw untrusted XML/HTML."""
    root = ET.parse(icon_path(name)).getroot()
    assert root.attrib['viewBox'] == '0 0 24 24'
    filled = root.get('fill') != 'none'
    accepted = {'path', 'rect', 'circle', 'polyline', 'polygon', 'line'}
    fields = {'d', 'x', 'y', 'cx', 'cy', 'r', 'rx', 'ry', 'width', 'height',
              'x1', 'x2', 'y1', 'y2', 'points', 'stroke-dasharray'}
    parts = []
    for element in root:
        tag = element.tag.rsplit('}', 1)[-1]
        if tag not in accepted or set(element.attrib) - fields or list(element):
            raise ValueError(f'{name}: unsupported SVG icon element')
        parts.append((tag, tuple(sorted(element.attrib.items()))))
    if not parts:
        raise ValueError(f'{name}: empty SVG icon')
    return filled, tuple(parts)


def embedded_icon(name: str, *, x: float, y: float, size: float, color: str) -> str:
    """Embed a 24-unit icon directly in a standalone SVG storyboard frame."""
    from xml.sax.saxutils import escape
    filled, elements = icon_art(name)
    color = escape(color, {'"': '&quot;'})
    style = f'fill="{color}" stroke="none"' if filled else (
        f'fill="none" stroke="{color}" stroke-width="1.7" '
        'stroke-linejoin="round" stroke-linecap="round"')
    chunks = [f'<g transform="translate({x-size/2:.2f} {y-size/2:.2f}) '
              f'scale({size/24:.4f})" {style}>']
    for tag, attrs in elements:
        attributes = ' '.join(
            f'{k}="{escape(v, {chr(34): "&quot;"})}"' for k,v in attrs)
        chunks.append(f'<{tag} {attributes}/>')
    return ''.join(chunks) + '</g>'
