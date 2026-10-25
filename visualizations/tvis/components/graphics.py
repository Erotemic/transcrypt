"""Small Manim drawing primitives used by DiagramScene.

No global Manim monkeypatching. Render output and texture caches are confined
under ``visualizations/.build`` by the CLI, not managed by the scene code.
"""
from __future__ import annotations

import numpy as np
from manim import (
    Arrow, DashedVMobject, Line, RoundedRectangle, Text, VGroup,
    LEFT, RIGHT, UP, DOWN, SVGMobject,
)

from tvis.diagram import (Link, Node, Region, Processing, EVIDENCE_LABELS,
                          EVIDENCE_ROLES, PAYLOAD_LABELS, PAYLOAD_ROLES)
from tvis.icons import icon_name, icon_path, icon_art


def xy(point: tuple[float, float]) -> np.ndarray:
    return np.array([point[0], point[1], 0.0])


def _fit(text: Text, max_width: float):
    if text.width > max_width:
        text.scale(max_width / text.width)
    return text


def text_label(value: str, colors: dict, *, font_size: int = 23, color: str = 'foreground', max_width: float = 12.2):
    result = Text(value, font_size=font_size, color=colors[color])
    return _fit(result, max_width)


def node_card(n: Node, colors: dict) -> VGroup:
    box = RoundedRectangle(
        width=n.width, height=n.height, corner_radius=0.15,
        stroke_color=colors[n.role], stroke_width=2.6,
        fill_color=colors['surface'], fill_opacity=1.0,
    ).move_to(xy(n.xy))
    heading = Text(n.title, font_size=23, color=colors['foreground'], weight='BOLD')
    _fit(heading, n.width-0.92)
    heading.move_to(box.get_center()+RIGHT*0.35+UP*0.13)
    secondary = Text(n.subtitle, font_size=15, color=colors['muted'])
    _fit(secondary, n.width-0.92)
    secondary.move_to(box.get_center()+RIGHT*0.35+DOWN*0.26)
    name = icon_name(n)
    logo = SVGMobject(str(icon_path(name)))
    logo.set_height(min(0.47, n.height * 0.45))
    filled, _ = icon_art(name)
    if filled:
        logo.set_fill(colors[n.role], opacity=1)
        logo.set_stroke(width=0)
    else:
        logo.set_fill(opacity=0)
        logo.set_stroke(colors[n.role], width=2.2)
    logo.move_to(box.get_center() + LEFT*(n.width/2-0.37))
    group = VGroup(box, logo, heading, secondary)
    if n.tag:
        tag = Text(n.tag, font_size=11, color=colors[n.role], weight='BOLD')
        _fit(tag, n.width-0.25)
        tag.align_to(box, RIGHT).shift(LEFT*0.12)
        tag.align_to(box, UP).shift(DOWN*0.12)
        group.add(tag)
    if n.evidence:
        badge_color = colors[EVIDENCE_ROLES[n.evidence.level]]
        badge = RoundedRectangle(width=n.width-0.1, height=0.24, corner_radius=0.075,
                                 stroke_color=badge_color, stroke_width=1.9,
                                 fill_color=colors['surface_soft'], fill_opacity=1.0)
        badge.move_to(xy((n.xy[0], n.xy[1]-n.height/2-0.18)))
        label = Text(EVIDENCE_LABELS[n.evidence.level], font_size=11.5,
                     color=badge_color, weight='BOLD')
        _fit(label, n.width-0.24)
        label.move_to(badge.get_center())
        group.add(badge, label)
    return group


def processing_card(step: Processing, node: Node, colors: dict) -> VGroup:
    """A typed input -> operation -> output, directly under its evidence badge."""
    x = node.xy[0]
    y = node.xy[1]-node.height/2-0.55
    rect = RoundedRectangle(width=node.width-0.04, height=0.32,
                            corner_radius=0.09, fill_color=colors['surface_soft'],
                            fill_opacity=1, stroke_color=colors['neutral'], stroke_width=1.0)
    rect.move_to(xy((x,y)))
    bcolor = colors[PAYLOAD_ROLES[step.before_kind]]
    acolor = colors[PAYLOAD_ROLES[step.after_kind]]
    from manim import Dot
    before_dot = Dot(radius=0.05, color=bcolor).move_to(xy((x-node.width/2+0.14,y)))
    after_dot = Dot(radius=0.05, color=acolor).move_to(xy((x+0.14,y)))
    before = Text(step.before, font_size=12.5, color=colors['foreground'])
    _fit(before, node.width*0.37)
    before.move_to(xy((x-node.width*0.25+0.07,y)))
    arrow = Text('→', font_size=14, color=colors['muted']).move_to(xy((x,y)))
    after = Text(step.after, font_size=12.5, color=colors['foreground'])
    _fit(after, node.width*0.33)
    after.move_to(xy((x+node.width*0.27,y)))
    # Separate elements so Manim can reveal the input, then the result.
    return VGroup(rect, VGroup(before_dot, before), arrow, VGroup(after_dot, after))


def region_box(r: Region, colors: dict) -> VGroup:
    rect = RoundedRectangle(
        width=r.width, height=r.height, corner_radius=0.2,
        stroke_color=colors[r.role], stroke_width=1.5,
        fill_opacity=0,
    ).move_to(xy(r.xy))
    if r.dashed:
        rect = DashedVMobject(rect, num_dashes=36, dashed_ratio=0.65)
    title = Text(r.title, font_size=14, weight='BOLD', color=colors[r.role])
    title.move_to(xy((r.xy[0]-r.width/2+0.25, r.xy[1]+r.height/2-0.23)))
    # Anchor text by its left edge, not its center.
    title.shift(RIGHT * title.width/2)
    return VGroup(rect, title)


def link_path(edge: Link):
    """A drawable path shared by link animation and traveling packet."""
    from manim import VMobject
    path = VMobject()
    path.set_points_as_corners([xy(pt) for pt in edge.path])
    return path


def edge_group(edge: Link, colors: dict) -> VGroup:
    from manim import DashedLine
    points = [xy(pt) for pt in edge.path]
    segments = VGroup()
    for start, end in zip(points[:-2], points[1:-1]):
        if edge.dashed:
            segments.add(DashedLine(start, end, dash_length=0.09,
                                    color=colors[edge.role], stroke_width=2.6))
        else:
            segments.add(Line(start, end, color=colors[edge.role], stroke_width=2.6))
    arrow = Arrow(points[-2], points[-1], buff=0,
                  color=colors[edge.role], stroke_width=2.7,
                  max_tip_length_to_length_ratio=0.17)
    segments.add(arrow)
    if edge.label:
        label = Text(edge.label, font_size=15, color=colors[edge.role])
        _fit(label, 2.75)
        if edge.label_xy is not None:
            label.move_to(xy(edge.label_xy))
        else:
            label.move_to((points[0]+points[-1])*0.5 + UP*0.27)
        segments.add(label)
    return segments


# Protocol annotations. The SVG renderer and Manim both use the pure
# layer_geometry function so editable nested rectangles stay in register.
def knowledge_card(entry, owner, colors):
    from manim import Circle
    box = RoundedRectangle(width=entry.width, height=entry.height,
                           corner_radius=0.13, stroke_color=colors[owner.role],
                           stroke_width=1.8, fill_color=colors['surface'],
                           fill_opacity=1).move_to(xy(entry.xy))
    heading = Text(owner.title + ' has', font_size=17,
                   color=colors[owner.role], weight='BOLD')
    _fit(heading, entry.width-0.30)
    heading.move_to(box.get_top()+DOWN*0.23)
    # Left edge 0.14 inside the card (align_to already places the left edge).
    heading.align_to(box, LEFT).shift(RIGHT*0.14)
    entries = VGroup()
    for idx, value in enumerate(entry.items):
        row = Text(value, font_size=15, color=colors['foreground'])
        _fit(row, entry.width-0.55)
        y = entry.xy[1] + entry.height/2-0.57-idx*0.27
        row.move_to(xy((entry.xy[0]-entry.width/2+0.38+row.width/2, y)))
        marker = Circle(radius=0.036, fill_color=colors[owner.role],
                        stroke_width=0, fill_opacity=1).move_to(
                            xy((entry.xy[0]-entry.width/2+0.22,y)))
        entries.add(marker,row)
    return VGroup(box,heading,entries)


def package_group(package, colors):
    from tvis.diagram import layer_geometry
    layer_colors = {'plain':'neutral', 'signed':'policy',
                    'encrypted':'guest', 'sealed':'broker', 'private':'secret'}
    shells = VGroup()
    for layer, center, width, height in layer_geometry(package):
        tint = colors[layer_colors[layer.kind]]
        shell = RoundedRectangle(width=width, height=height,
                                 corner_radius=0.12, stroke_color=tint,
                                 stroke_width=2.0, fill_color=colors['surface'],
                                 fill_opacity=1.0).move_to(xy(center))
        title = Text(layer.title, font_size=17, color=tint, weight='BOLD')
        _fit(title,width-0.32)
        title.move_to(shell.get_top()+DOWN*0.25)
        title.align_to(shell, LEFT).shift(RIGHT*(0.15+title.width/2))
        note = Text(layer.note, font_size=12, color=colors['muted'])
        _fit(note,width-0.32)
        note.move_to(shell.get_top()+DOWN*0.46)
        note.align_to(shell, LEFT).shift(RIGHT*(0.15+note.width/2))
        shells.add(VGroup(shell,title,note))
    return shells


def traveling_label(title, kind, colors):
    from manim import Circle
    color=colors[PAYLOAD_ROLES[kind]]
    if not title:
        return Circle(radius=0.065, color=color, fill_opacity=1.0,
                      stroke_width=0)
    content = Text(title, font_size=14, color=colors['foreground'], weight='BOLD')
    _fit(content, 2.12)
    kind_label=Text(PAYLOAD_LABELS[kind],font_size=10,color=colors['background'],weight='BOLD')
    swatch=RoundedRectangle(width=0.53,height=0.23,corner_radius=0.065,
                            stroke_width=0,fill_color=color,fill_opacity=1.0)
    kind_label.move_to(swatch.get_center())
    bg = RoundedRectangle(width=max(content.width+0.95,1.35),height=0.33,
                          corner_radius=0.11,stroke_color=color,stroke_width=2,
                          fill_color=colors['surface_soft'],fill_opacity=1.0)
    swatch.move_to(bg.get_left()+RIGHT*0.35)
    kind_label.move_to(swatch.get_center())
    content.move_to(bg.get_center()+RIGHT*0.30)
    return VGroup(bg,swatch,kind_label,content)
