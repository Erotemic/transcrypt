"""Manim entrypoint for the lock operation storyboard."""
from tvis.scene_base import DiagramScene
from tvis.plans.lock import PLAN


class LockAndFlushLifecycle(DiagramScene):
    PLAN = PLAN
