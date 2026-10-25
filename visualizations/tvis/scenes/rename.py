"""Manim entrypoint for the rename operation storyboard."""
from tvis.scene_base import DiagramScene
from tvis.plans.rename import PLAN


class PathRebindingLifecycle(DiagramScene):
    PLAN = PLAN
