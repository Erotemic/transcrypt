"""Manim entrypoint. Edit plans/status.py to change the authored beats."""
from tvis.scene_base import DiagramScene
from tvis.plans.status import PLAN


class VerificationStatus(DiagramScene):
    PLAN = PLAN
