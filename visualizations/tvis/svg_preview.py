"""Instant SVG views of the same nodes, packets and knowledge used by Manim."""
from __future__ import annotations

import math
import textwrap
from pathlib import Path
from xml.sax.saxutils import escape

from tvis.diagram import (Diagram, Node, Region, Link, Package, Knowledge,
                          Processing, EVIDENCE_LABELS, EVIDENCE_ROLES, PAYLOAD_LABELS,
                          PAYLOAD_ROLES, layer_geometry)
from tvis.palette import palette
from tvis.icons import embedded_icon, icon_name

CANVAS_W = 1440
CANVAS_H = 810
SCALE = 100
LAYER_COLORS = {'plain': 'neutral', 'signed': 'policy', 'encrypted': 'guest',
                'sealed': 'broker', 'private': 'secret'}
STATUS_ROLES = {'proved':'proved','modeled':'policy','tested':'broker',
                'assumed':'assumed','planned':'open','open':'open'}
STATUS_LABELS = {'explainer': 'EXPLANATION', 'implemented': 'IN CODE',
                 'proved': 'SOURCE-DERIVED PROOF', 'modeled': 'MODEL PROOF',
                 'tested': 'TESTED', 'assumed': 'TRUSTED PREMISE',
                 'planned': 'DESIGN GOAL', 'open': 'NOT YET PROVEN'}


def sx(x: float) -> float:
    return CANVAS_W/2 + x*SCALE


def sy(y: float) -> float:
    return CANVAS_H/2 - y*SCALE


def _xml(text: str) -> str:
    return escape(text, {'"': '&quot;', "'": '&apos;'})


def _node(n: Node, colors: dict, *, highlight: bool) -> str:
    x, y = sx(n.xy[0]), sy(n.xy[1])
    w, h = n.width*SCALE, n.height*SCALE
    stroke = colors[n.role]
    icon_x = x - w/2 + 35
    text_x = x + 35
    # Approximate SVG font metrics and reserve left space for the icon.
    # Manim makes the equivalent adjustment with measured Text.width.
    available = max(75.0, w - 94.0)
    heading_size = min(22.0, max(12.0, available / (max(1, len(n.title)) * 0.60)))
    parts = [f'<rect x="{x-w/2:.1f}" y="{y-h/2:.1f}" width="{w:.1f}" height="{h:.1f}" rx="14" '
             f'fill="{colors["surface"]}" stroke="{stroke}" stroke-width="{4 if highlight else 2.4}"/>',
             embedded_icon(icon_name(n), x=icon_x, y=y-1, size=45, color=stroke),
             f'<text x="{text_x:.1f}" y="{y-3:.1f}" text-anchor="middle" font-weight="600" '
             f'font-size="{heading_size:.1f}" fill="{colors["foreground"]}">{_xml(n.title)}</text>']
    for i, line in enumerate(textwrap.wrap(n.subtitle, width=max(12, int(available/8.4)))[:2]):
        subtitle_size = min(14.0, max(10.0, available / (max(1, len(line)) * 0.62)))
        parts.append(f'<text x="{text_x:.1f}" y="{y+24+i*16:.1f}" text-anchor="middle" font-size="{subtitle_size:.1f}" '
                     f'fill="{colors["muted"]}">{_xml(line)}</text>')
    if n.tag:
        parts.append(f'<text x="{x+w/2-9:.1f}" y="{y-h/2+13:.1f}" text-anchor="end" '
                     f'font-size="11" font-weight="700" fill="{stroke}">{_xml(n.tag)}</text>')
    if n.evidence:
        evidence = n.evidence
        color = colors[EVIDENCE_ROLES[evidence.level]]
        badge_y = y+h/2+18
        badge_w = w-10
        parts += [f'<g data-evidence="{_xml(evidence.level)}" data-operation="{_xml(n.key)}">',
                  f'<title>{_xml(evidence.basis + ": " + evidence.note)}</title>',
                  f'<rect x="{x-badge_w/2:.1f}" y="{badge_y-12:.1f}" width="{badge_w:.1f}" height="24" rx="8" '
                  f'fill="{colors["surface_soft"]}" stroke="{color}" stroke-width="2"/>',
                  f'<text x="{x:.1f}" y="{badge_y+4:.1f}" text-anchor="middle" font-size="12" '
                  f'font-weight="700" fill="{color}">{_xml(EVIDENCE_LABELS[evidence.level])}</text>', '</g>']
    return '\n'.join(parts)


def _processing(step: Processing, node: Node, colors: dict) -> str:
    x = sx(node.xy[0])
    y = sy(node.xy[1]-node.height/2-0.55)
    w = node.width*100 - 4
    ink = colors['foreground']
    bcolor = colors[PAYLOAD_ROLES[step.before_kind]]
    acolor = colors[PAYLOAD_ROLES[step.after_kind]]
    def clipped(s: str, max_len: int = 11) -> str:
        return _xml(textwrap.shorten(s, width=max_len, placeholder='…'))
    return (f'<g data-processing="{_xml(step.node)}" data-input="{_xml(step.before_kind)}" '
            f'data-output="{_xml(step.after_kind)}">'
            f'<rect x="{x-w/2:.1f}" y="{y-16:.1f}" width="{w:.1f}" height="32" rx="9" '
            f'fill="{colors["surface_soft"]}" stroke="{colors["neutral"]}" stroke-opacity=".65"/> '
            f'<circle cx="{x-w/2+12:.1f}" cy="{y:.1f}" r="5" fill="{bcolor}"/> '
            f'<text x="{x-w/2+22:.1f}" y="{y+4:.1f}" font-size="12" fill="{ink}">{clipped(step.before)}</text>'
            f'<text x="{x:.1f}" y="{y+4:.1f}" text-anchor="middle" font-size="13" fill="{colors["muted"]}">→</text>'
            f'<circle cx="{x+7:.1f}" cy="{y:.1f}" r="5" fill="{acolor}"/> '
            f'<text x="{x+17:.1f}" y="{y+4:.1f}" font-size="12" fill="{ink}">{clipped(step.after)}</text>'
            f'</g>')


def _region(r: Region, colors: dict) -> str:
    x, y = sx(r.xy[0]), sy(r.xy[1])
    w, h = r.width*SCALE, r.height*SCALE
    dashed = 'stroke-dasharray="10 11"' if r.dashed else ''
    return (f'<rect x="{x-w/2:.1f}" y="{y-h/2:.1f}" width="{w:.1f}" height="{h:.1f}" rx="20" '
            f'fill="{colors["broker"]}" fill-opacity="0.018" stroke="{colors[r.role]}" '
            f'stroke-opacity="0.6" stroke-width="2" {dashed}/>'
            f'<text x="{x-w/2+18:.1f}" y="{y-h/2+26:.1f}" font-size="13" '
            f'fill="{colors[r.role]}" font-weight="700">{_xml(r.title)}</text>')


def _link(e: Link, colors: dict, *, highlight: bool) -> str:
    points = [(sx(x), sy(y)) for x,y in e.path]
    stroke = colors[e.role]
    coords = ' '.join(f'{x:.1f},{y:.1f}' for x,y in points)
    dash = 'stroke-dasharray="9 8"' if e.dashed else ''
    parts = [f'<polyline points="{coords}" stroke="{stroke}" fill="none" '
             f'stroke-width="{4 if highlight else 2.7}" stroke-linejoin="round" '
             f'stroke-linecap="round" {dash}/>']
    x0,y0 = points[-2]; x1,y1 = points[-1]
    length = math.hypot(x1-x0, y1-y0)
    ux,uy = (x1-x0)/length,(y1-y0)/length
    ax,ay = x1-ux*14,y1-uy*14
    px,py = -uy,ux
    parts.append(f'<polygon points="{x1:.1f},{y1:.1f} {ax+px*6:.1f},{ay+py*6:.1f} '
                 f'{ax-px*6:.1f},{ay-py*6:.1f}" fill="{stroke}"/>')
    if e.label:
        mx,my = e.label_xy or ((e.path[0][0]+e.path[-1][0])/2,
                                (e.path[0][1]+e.path[-1][1])/2+0.26)
        lx,ly=sx(mx),sy(my)
        bw = min(300,max(46,len(e.label)*8.0+18))
        parts.append(f'<rect x="{lx-bw/2:.1f}" y="{ly-17:.1f}" width="{bw:.1f}" '
                     f'height="22" rx="6" fill="{colors["background"]}" fill-opacity=".96"/>')
        parts.append(f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" font-size="14" '
                     f'fill="{stroke}">{_xml(e.label)}</text>')
    return '\n'.join(parts)


def _package(item: Package, colors: dict, *, focus: str, depth: int) -> str:
    result: list[str] = []
    for level, (layer, xy, width, height) in enumerate(layer_geometry(item)[:depth+1]):
        x,y = sx(xy[0]),sy(xy[1]); w,h=width*SCALE,height*SCALE
        tint = colors[LAYER_COLORS[layer.kind]]
        result.append(f'<rect x="{x-w/2:.1f}" y="{y-h/2:.1f}" width="{w:.1f}" height="{h:.1f}" '
                      f'rx="12" fill="{colors["surface"]}" stroke="{tint}" '
                      f'stroke-width="{4 if layer.key==focus else 2.2}"/>')
        # Each nesting level gets its own visible header strip.
        left=x-w/2+14
        result.append(f'<text x="{left:.1f}" y="{y-h/2+27:.1f}" font-size="18" '
                      f'font-weight="650" fill="{tint}">{_xml(layer.title)}</text>')
        if layer.note:
            result.append(f'<text x="{left:.1f}" y="{y-h/2+47:.1f}" font-size="13" '
                          f'fill="{colors["muted"]}">{_xml(layer.note)}</text>')
    return '\n'.join(result)


def _knowledge(entry: Knowledge, colors: dict, owner_role: str, owner_title: str) -> str:
    x,y=sx(entry.xy[0]),sy(entry.xy[1]); w,h=entry.width*SCALE,entry.height*SCALE
    tint=colors[owner_role]
    result=[f'<rect x="{x-w/2:.1f}" y="{y-h/2:.1f}" width="{w:.1f}" height="{h:.1f}" '
            f'rx="14" fill="{colors["surface"]}" stroke="{tint}" stroke-opacity=".75" stroke-width="2"/>',
            f'<text x="{x-w/2+15:.1f}" y="{y-h/2+29:.1f}" font-size="16" '
            f'font-weight="700" fill="{tint}">{_xml(owner_title)} has</text>']
    for i, line in enumerate(entry.items):
        yline=y-h/2+58+min(i,5)*27
        # A complete snapshot; the input is literal human-readable data labels.
        text = textwrap.shorten(line, width=int(w/8.3), placeholder='…')
        result.append(f'<circle cx="{x-w/2+22:.1f}" cy="{yline-5:.1f}" r="3.5" fill="{tint}"/>')
        result.append(f'<text x="{x-w/2+36:.1f}" y="{yline:.1f}" font-size="17" '
                      f'fill="{colors["foreground"]}">{_xml(text)}</text>')
    return '\n'.join(result)


def _travel_marker(link: Link, label: str, kind: str, colors: dict) -> str:
    # Halfway along true multi-segment length; never just average endpoints.
    pts = [(sx(x),sy(y)) for x,y in link.path]
    segments = [math.dist(a,b) for a,b in zip(pts[:-1],pts[1:])]
    half=sum(segments)/2
    for index, d in enumerate(segments):
        if half <= d:
            start,end=pts[index:index+2]
            portion=half/d
            px=start[0]+(end[0]-start[0])*portion
            py=start[1]+(end[1]-start[1])*portion
            break
        half-=d
    else:
        px,py=pts[-1]
    text=label or 'request'
    tint=colors[PAYLOAD_ROLES[kind]]
    category=PAYLOAD_LABELS[kind]
    width=max(115,min(330,len(text)*8.1+67))
    return (f'<g data-payload-kind="{_xml(kind)}">'
            f'<rect x="{px-width/2:.1f}" y="{py-17:.1f}" width="{width:.1f}" height="32" '
            f'rx="11" fill="{colors["surface_soft"]}" stroke="{tint}" stroke-width="2.5"/>'
            f'<rect x="{px-width/2+4:.1f}" y="{py-12:.1f}" width="42" height="22" rx="6" fill="{tint}"/>'
            f'<text x="{px-width/2+25:.1f}" y="{py+3:.1f}" text-anchor="middle" font-size="9" '
            f'font-weight="700" fill="{colors["background"]}">{category}</text>'
            f'<text x="{px+23:.1f}" y="{py+4:.1f}" font-size="13" font-weight="650" '
            f'text-anchor="middle" fill="{colors["foreground"]}">{_xml(text)}</text></g>')


def render_svg(plan: Diagram, *, beat: int | str = 'last', theme: str = 'dark') -> str:
    colors=palette(theme)
    nodes,links,stage,index=plan.state(beat)
    pieces=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{CANVAS_W}" height="{CANVAS_H}" '
            f'viewBox="0 0 {CANVAS_W} {CANVAS_H}">',
            f'<rect width="100%" height="100%" fill="{colors["background"]}"/>',
            f'<text x="76" y="67" font-size="40" font-weight="700" '
            f'fill="{colors["foreground"]}">{_xml(plan.title)}</text>',
            f'<text x="76" y="100" font-size="18" fill="{colors["muted"]}">{_xml(plan.kicker)}</text>',
            f'<text x="1360" y="70" text-anchor="end" font-size="17" font-weight="700" '
            f'fill="{colors[STATUS_ROLES.get(stage.status, "policy")]}">{STATUS_LABELS[stage.status]}</text>',
            f'<text x="1360" y="98" text-anchor="end" font-size="16" '
            f'fill="{colors["muted"]}">{index+1} / {len(plan.beats)}</text>']
    for region in plan.regions:
        pieces.append(_region(region,colors))
    for link in links:
        pieces.append(_link(link,colors,highlight=link.key in stage.focus))
    for node in nodes:
        pieces.append(_node(node,colors,highlight=node.key in stage.focus))
    for pack in plan.visible_packages(index):
        pieces.append(_package(pack,colors,focus=stage.layer_focus,depth=plan.visible_layer_depth(pack.key,index)))
    if stage.processing:
        pieces.append(_processing(stage.processing, plan.node_map()[stage.processing.node], colors))
    for knowledge in stage.knowledge:
        owner=plan.node_map()[knowledge.owner]
        pieces.append(_knowledge(knowledge,colors,owner.role,owner.title))
    if stage.packet:
        pieces.append(_travel_marker(plan.link_map()[stage.packet],stage.packet_label,stage.packet_kind,colors))
    pieces += [f'<rect x="70" y="663" width="1300" height="90" rx="15" '
               f'fill="{colors["surface_soft"]}" stroke="{colors["neutral"]}" stroke-opacity=".2"/>',
               f'<text x="92" y="690" font-size="15" font-weight="700" '
               f'fill="{colors["policy"]}">{_xml(stage.key.upper())}</text>']
    for i,line in enumerate(textwrap.wrap(stage.caption,width=94)[:2]):
        pieces.append(f'<text x="92" y="{715+i*24}" font-size="20" '
                      f'fill="{colors["foreground"]}">{_xml(line)}</text>')
    pieces += [f'<text x="76" y="790" font-size="14" fill="{colors["muted"]}">{_xml(plan.footer)}</text>',
               '</svg>']
    return '\n'.join(pieces)


def write_preview(plan: Diagram, out: Path, *, beat: int | str = 'last', theme: str = 'dark') -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_svg(plan, beat=beat, theme=theme), encoding='utf-8')
    return out
