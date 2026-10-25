"""Manim entrypoint for the unlock operation storyboard."""
from tvis.scene_base import DiagramScene
from tvis.plans.unlock import PLAN


class UnlockKeyLifecycle(DiagramScene):
    PLAN = PLAN
