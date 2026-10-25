"""Editable Transcrypt protocol diagrams shared by SVG and Manim.

Coordinates are Manim units on a 14.22 x 8.0 frame. This is presentation
source, not executable broker code or a substitute for a cryptography model.

The small components are intentionally explicit: parties, links, snapshots of
what a party knows, and nested packages. To edit a scene, edit its PLAN in
``tvis/plans/<scene>.py``; no second render-specific layout is needed.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from tvis.palette import ROLES

Point = tuple[float, float]
LayerKind = Literal['plain', 'signed', 'encrypted', 'sealed', 'private']
BeatStatus = Literal['explainer', 'implemented', 'proved', 'modeled', 'tested', 'assumed', 'planned', 'open']


@dataclass(frozen=True)
class Node:
    key: str
    title: str
    subtitle: str
    xy: Point
    width: float = 2.55
    height: float = 1.12
    role: str = 'neutral'
    tag: str = ''
    icon: str = ''  # see tvis/icons.py; inferred from role when empty


@dataclass(frozen=True)
class Region:
    key: str
    title: str
    xy: Point
    width: float
    height: float
    role: str = 'broker'
    dashed: bool = True


@dataclass(frozen=True)
class Link:
    key: str
    origin: str
    destination: str
    label: str
    path: tuple[Point, ...]
    role: str = 'neutral'
    dashed: bool = False
    label_xy: Point | None = None


@dataclass(frozen=True)
class Layer:
    """One concentric box in an *explanatory* packet cross-section.

    ``inner`` is hidden inside the preceding wrapped/encrypted layer; it is
    shown to the human viewer as an X-ray diagram, not as guest-readable text.
    Plain/signed do not imply confidentiality. Encrypted/sealed do not imply a
    proof of the crypto adapter or of key custody in the operating system.
    """
    key: str
    title: str
    note: str
    kind: LayerKind
    inner: 'Layer | None' = None


@dataclass(frozen=True)
class Package:
    key: str
    xy: Point
    width: float
    height: float
    outer: Layer


def layer_geometry(package: Package) -> tuple[tuple[Layer, Point, float, float], ...]:
    """Calculate concentric rectangles without importing any renderer."""
    data = []
    layer = package.outer
    x, y = package.xy
    width, height = package.width, package.height
    while layer is not None:
        data.append((layer, (x, y), width, height))
        # Reserve a separate header strip for each nesting level.
        width -= 0.36
        height -= 0.77
        y -= 0.365
        layer = layer.inner
    return tuple(data)


@dataclass(frozen=True)
class Knowledge:
    """Complete *current* holdings of one party at one animation beat.

    This is a snapshot, not an accumulated list: sending information does not
    magically delete the sender's copy. No implication that absence here proves
    secrecy outside the illustrated protocol boundary.
    """
    owner: str
    xy: Point
    items: tuple[str, ...]
    width: float = 3.46
    height: float = 2.36


@dataclass(frozen=True)
class Beat:
    key: str
    caption: str
    nodes: tuple[str, ...] = ()
    links: tuple[str, ...] = ()
    focus: tuple[str, ...] = ()
    packet: str = ''
    duration: float = 1.2
    hold: float = 0.6
    # The text travels along ``packet`` and is also displayed in a still.
    packet_label: str = ''
    # Only the active beat's knowledge is shown; it replaces the previous beat.
    knowledge: tuple[Knowledge, ...] = ()
    # Package panels are cumulative, like nodes/links.
    packages: tuple[str, ...] = ()
    # Optional layer highlight for the current explanatory beat.
    layer_focus: str = ''
    status: BeatStatus = 'explainer'


@dataclass(frozen=True)
class Diagram:
    key: str
    title: str
    kicker: str
    nodes: tuple[Node, ...]
    links: tuple[Link, ...]
    beats: tuple[Beat, ...]
    regions: tuple[Region, ...] = ()
    packages: tuple[Package, ...] = ()
    footer: str = ''

    def node_map(self) -> dict[str, Node]:
        return {node.key: node for node in self.nodes}

    def link_map(self) -> dict[str, Link]:
        return {link.key: link for link in self.links}

    def package_map(self) -> dict[str, Package]:
        return {item.key: item for item in self.packages}

    def beat_names(self) -> tuple[str, ...]:
        return tuple(b.key for b in self.beats)

    def state(self, beat: int | str = 'last') -> tuple[list[Node], list[Link], Beat, int]:
        """Backward-compatible node/link visibility and active beat."""
        if not self.beats:
            raise ValueError(f'{self.key}: no beats')
        if beat == 'last':
            index = len(self.beats) - 1
        elif isinstance(beat, int):
            index = beat
        else:
            try:
                index = self.beat_names().index(beat)
            except ValueError as ex:
                raise ValueError(f'unknown beat {beat!r}; use {self.beat_names()!r}') from ex
        if not 0 <= index < len(self.beats):
            raise ValueError(f'beat index {index} out of range')
        seen_nodes: set[str] = set()
        seen_links: set[str] = set()
        for step in self.beats[:index + 1]:
            seen_nodes.update(step.nodes)
            seen_links.update(step.links)
        return ([node for node in self.nodes if node.key in seen_nodes],
                [link for link in self.links if link.key in seen_links],
                self.beats[index], index)

    def visible_packages(self, beat: int | str = 'last') -> list[Package]:
        _, _, _, index = self.state(beat)
        shown = {key for stage in self.beats[:index+1] for key in stage.packages}
        return [item for item in self.packages if item.key in shown]

    def visible_layer_depth(self, package_key: str, beat: int | str = 'last') -> int:
        """Deepest revealed nested layer, using beat.layer_focus as a reveal cue."""
        package = self.package_map()[package_key]
        layers = [layer.key for layer, *_ in layer_geometry(package)]
        _, _, _, index = self.state(beat)
        depth = -1
        for stage in self.beats[:index+1]:
            if package_key in stage.packages and depth < 0:
                depth = 0 if stage.layer_focus in layers else len(layers)-1
            if stage.layer_focus in layers:
                depth = max(depth, layers.index(stage.layer_focus))
        return depth


def _inside(xy: Point, width: float, height: float, *, limit_y: float = 2.66) -> bool:
    return (abs(xy[0]) + width/2 <= 6.91 and
            abs(xy[1]) + height/2 <= limit_y)


def validate(plan: Diagram) -> None:
    """Reject broken plan IDs, implausible cryptographic notation and overlap.

    The layout bounds are not a typography renderer. Inspect SVG/Manim output
    when changing text length or font faces.
    """
    if not plan.title.strip() or not plan.beats:
        raise ValueError(f'{plan.key}: missing title or beats')
    for kind, ids in [('node', [x.key for x in plan.nodes]),
                      ('link', [x.key for x in plan.links]),
                      ('region', [x.key for x in plan.regions]),
                      ('package', [x.key for x in plan.packages]),
                      ('beat', [x.key for x in plan.beats])]:
        if len(ids) != len(set(ids)) or any(not key for key in ids):
            raise ValueError(f'{plan.key}: duplicate/empty {kind} ID')
    nodes = plan.node_map()
    links = plan.link_map()
    packages = plan.package_map()
    layer_ids = set()
    from tvis.icons import icon_name, icon_art
    for node in plan.nodes:
        icon_art(icon_name(node))
        if node.role not in ROLES or node.width <= 0 or node.height <= 0:
            raise ValueError(f'{plan.key}: invalid node {node.key}')
        if not _inside(node.xy, node.width, node.height):
            raise ValueError(f'{plan.key}: node {node.key} clipped')
    for edge in plan.links:
        if edge.role not in ROLES or len(edge.path) < 2:
            raise ValueError(f'{plan.key}: invalid link {edge.key}')
        if edge.origin not in nodes or edge.destination not in nodes:
            raise ValueError(f'{plan.key}: missing endpoint for link {edge.key}')
        if any(abs(x) > 7.0 or abs(y) > 2.85 for x, y in edge.path):
            raise ValueError(f'{plan.key}: link {edge.key} clipped')
        for pt, endpoint in ((edge.path[0], nodes[edge.origin]),
                             (edge.path[-1], nodes[edge.destination])):
            dx = abs(pt[0] - endpoint.xy[0])
            dy = abs(pt[1] - endpoint.xy[1])
            x_edge = abs(dx - endpoint.width/2) if dy <= endpoint.height/2+0.24 else 100
            y_edge = abs(dy - endpoint.height/2) if dx <= endpoint.width/2+0.24 else 100
            if min(x_edge, y_edge) > 0.24:
                raise ValueError(f'{plan.key}: arrow {edge.key} misses {endpoint.key}')
    for region in plan.regions:
        if region.role not in ROLES or region.width <= 0 or region.height <= 0:
            raise ValueError(f'{plan.key}: invalid region {region.key}')
    for package in plan.packages:
        if not _inside(package.xy, package.width, package.height) or package.width < 2 or package.height < 1:
            raise ValueError(f'{plan.key}: package {package.key} clipped')
        boxes = layer_geometry(package)
        if len(boxes) > 5 or boxes[-1][2] <= 1.3 or boxes[-1][3] < 0.59:
            raise ValueError(f'{plan.key}: nested layers too deep in {package.key}')
        for layer, _, _, _ in boxes:
            if (layer.key in layer_ids or not layer.key or not layer.title or
                    layer.kind not in {'plain', 'signed', 'encrypted', 'sealed', 'private'}):
                raise ValueError(f'{plan.key}: invalid/duplicate package layer {layer.key}')
            layer_ids.add(layer.key)
    known_nodes: set[str] = set()
    known_links: set[str] = set()
    known_packages: set[str] = set()
    for stage in plan.beats:
        if not stage.caption or stage.duration <= 0 or stage.hold < 0:
            raise ValueError(f'{plan.key}: invalid beat {stage.key}')
        if stage.status not in {'explainer','implemented','proved','modeled','tested','assumed','planned','open'}:
            raise ValueError(f'{plan.key}: invalid status {stage.status}')
        if set(stage.nodes) - nodes.keys() or set(stage.links) - links.keys():
            raise ValueError(f'{plan.key}: unknown node/link in beat {stage.key}')
        if set(stage.packages) - packages.keys():
            raise ValueError(f'{plan.key}: missing package in beat {stage.key}')
        known_nodes.update(stage.nodes)
        known_links.update(stage.links)
        known_packages.update(stage.packages)
        for key in known_links:
            e = links[key]
            if e.origin not in known_nodes or e.destination not in known_nodes:
                raise ValueError(f'{plan.key}: link {key} visible before endpoints')
        if not set(stage.focus) <= known_nodes | known_links:
            raise ValueError(f'{plan.key}: focus not visible in {stage.key}')
        if stage.packet and stage.packet not in known_links:
            raise ValueError(f'{plan.key}: moving packet route not visible in {stage.key}')
        if stage.packet_label and not stage.packet:
            raise ValueError(f'{plan.key}: moving packet text without route')
        if stage.layer_focus and stage.layer_focus not in layer_ids:
            raise ValueError(f'{plan.key}: unknown package layer {stage.layer_focus}')
        if stage.layer_focus and not any(
                any(layer.key == stage.layer_focus for layer, *_ in layer_geometry(p))
                for p in plan.packages if p.key in known_packages):
            raise ValueError(f'{plan.key}: layer {stage.layer_focus} not yet shown')
        owners = [knowledge.owner for knowledge in stage.knowledge]
        if len(owners) != len(set(owners)):
            raise ValueError(f'{plan.key}: duplicate knowledge holders in {stage.key}')
        for entry in stage.knowledge:
            if entry.owner not in known_nodes:
                raise ValueError(f'{plan.key}: unknown knowledge owner {entry.owner}')
            if not entry.items or len(entry.items) > 5 or not _inside(entry.xy, entry.width, entry.height):
                raise ValueError(f'{plan.key}: invalid knowledge panel {entry.owner}')
    if set(nodes) != known_nodes or set(links) != known_links or set(packages) != known_packages:
        raise ValueError(f'{plan.key}: unreachable diagram elements')
