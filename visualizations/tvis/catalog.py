"""One readable TOML storyboard. No Manim import or plugin discovery."""
from __future__ import annotations

import ast
from dataclasses import dataclass
from importlib import import_module
from pathlib import Path
import tomllib

from tvis.diagram import Diagram, validate

VIS_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = VIS_ROOT.parent
STORYBOARD = VIS_ROOT / 'storyboards/overview.toml'
STATUSES = {'architecture', 'source-derived-proof', 'model-proof', 'runtime-tested', 'external-assumption', 'design-goal'}


@dataclass(frozen=True)
class SceneInfo:
    id: str
    file: str
    class_name: str
    plan: str
    status: str
    claim: str
    narration: str
    sources: tuple[str, ...]
    optional_sources: tuple[str, ...] = ()
    proof_anchors: tuple[str, ...] = ()

    def scene_path(self) -> Path:
        return VIS_ROOT / self.file

    def diagram(self) -> Diagram:
        diagram = import_module(self.plan).PLAN
        if not isinstance(diagram, Diagram) or diagram.key != self.id:
            raise ValueError(f'{self.id}: plan key/type disagrees with storyboard')
        validate(diagram)
        return diagram


def load_catalog(path: Path = STORYBOARD) -> tuple[dict, tuple[SceneInfo, ...]]:
    doc = tomllib.loads(path.read_text(encoding='utf-8'))
    deck = doc['deck']
    scenes = tuple(SceneInfo(
        id=s['id'], file=s['file'], class_name=s['class'], plan=s['plan'],
        status=s['status'], claim=s['claim'], narration=s['narration'],
        sources=tuple(s.get('sources', [])),
        optional_sources=tuple(s.get('optional_sources', [])),
        proof_anchors=tuple(s.get('proof_anchors', [])),
    ) for s in doc['scene'])
    if not scenes or len(set(s.id for s in scenes)) != len(scenes):
        raise ValueError('storyboard has duplicate or missing scene IDs')
    return deck, scenes


def get_scene(scene_id: str) -> SceneInfo:
    _, scenes = load_catalog()
    for scene in scenes:
        if scene.id == scene_id:
            return scene
    raise ValueError(f'unknown scene {scene_id!r}; choose: {", ".join(s.id for s in scenes)}')


def validate_catalog() -> tuple[SceneInfo, ...]:
    _, scenes = load_catalog()
    for scene in scenes:
        if scene.status not in STATUSES or not scene.claim.strip() or not scene.narration.strip():
            raise ValueError(f'{scene.id}: missing classification / claim / narration')
        source_path = scene.scene_path()
        if not source_path.is_file():
            raise ValueError(f'{scene.id}: missing Manim entrypoint {scene.file}')
        syntax = ast.parse(source_path.read_text(), filename=str(source_path))
        classes = {x.name for x in syntax.body if isinstance(x, ast.ClassDef)}
        if scene.class_name not in classes:
            raise ValueError(f'{scene.id}: Manim class {scene.class_name} not in {scene.file}')
        for rel in scene.sources + scene.optional_sources:
            path = (REPO_ROOT / rel).resolve()
            if not path.is_relative_to(REPO_ROOT):
                raise ValueError(f'{scene.id}: source ref escapes repository: {rel}')
            if rel in scene.sources and not path.is_file():
                raise ValueError(f'{scene.id}: missing evidence source {rel}')
        for anchor in scene.proof_anchors:
            theorem_name = anchor.rsplit('.', 1)[-1]
            if not theorem_name or not any(
                f'theorem {theorem_name}' in (REPO_ROOT / rel).read_text()
                for rel in scene.sources if rel.endswith('.lean')
            ):
                raise ValueError(f'{scene.id}: proof anchor {anchor} not found in referenced Lean sources')
        diagram = scene.diagram()
        # A green or purple per-operation badge must name a theorem in the
        # *same scene's* grounded source set, not merely reuse a scene status.
        for node in diagram.nodes:
            evidence = node.evidence
            if evidence and evidence.level in {'source-proof', 'conditional-proof', 'model-proof'}:
                if not any(f'theorem {evidence.basis}' in (REPO_ROOT / rel).read_text()
                           for rel in scene.sources if rel.endswith('.lean')):
                    raise ValueError(f'{scene.id}:{node.key}: missing evidence theorem {evidence.basis}')
    return scenes
