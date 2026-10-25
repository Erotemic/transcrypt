"""Reusable geometry; all coordinates feed both SVG and Manim."""
from __future__ import annotations

from dataclasses import replace

from tvis.diagram import Diagram, Knowledge, Link, Node

X3 = (-4.82, 0.0, 4.82)
X4 = (-5.24, -1.75, 1.75, 5.24)
Y = 1.63


def row3(items):
    """items: (key,title,subtitle,role,icon); 3 distinct roles."""
    return tuple(Node(k, title, sub, (x, Y), 2.72, 1.12, role, icon=icon)
                 for x, (k, title, sub, role, icon) in zip(X3, items, strict=True))


def row4(items):
    return tuple(Node(k, title, sub, (x, Y), 2.62, 1.10, role, icon=icon)
                 for x, (k, title, sub, role, icon) in zip(X4, items, strict=True))


def route(nodes, origin: str, destination: str, key: str, label: str, role: str):
    a = next(n for n in nodes if n.key == origin)
    b = next(n for n in nodes if n.key == destination)
    direction = 1 if b.xy[0] > a.xy[0] else -1
    return Link(key, origin, destination, label,
                ((a.xy[0] + direction * a.width / 2, a.xy[1]),
                 (b.xy[0] - direction * b.width / 2, b.xy[1])), role)


def info3(nodes, records):
    """Complete per-beat information snapshots; records align to row3 nodes."""
    return tuple(Knowledge(node.key, (x, -1.01), tuple(info), width=3.72, height=2.56)
                 for node, x, info in zip(nodes, X3, records, strict=True))


def info4(nodes, records):
    return tuple(Knowledge(node.key, (x, -1.01), tuple(info), width=3.08, height=2.56)
                 for node, x, info in zip(nodes, X4, records, strict=True))


def carry_knowledge(diagram: Diagram) -> Diagram:
    """Make omitted holdings mean unchanged, materializing complete snapshots.

    Both renderers still see an explicit *complete* Beat.knowledge tuple. The
    first beat with parties must provide the baseline; add a new snapshot to
    a later beat whenever a component's holdings actually change.
    """
    latest = ()
    beats = []
    for beat in diagram.beats:
        if beat.knowledge:
            latest = beat.knowledge
            beats.append(beat)
        else:
            beats.append(replace(beat, knowledge=latest) if latest else beat)
    return replace(diagram, beats=tuple(beats))
