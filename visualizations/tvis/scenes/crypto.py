"""Manim entrypoint for the crypto operation storyboard."""
from tvis.scene_base import DiagramScene
from tvis.plans.crypto import PLAN


class SealingCryptoBoundary(DiagramScene):
    PLAN = PLAN
