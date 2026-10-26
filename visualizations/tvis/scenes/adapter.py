"""Manim entrypoint. Edit plans/adapter.py to change the authored beats."""
from tvis.scene_base import DiagramScene
from tvis.plans.adapter import PLAN


class AdapterCorrespondence(DiagramScene):
    PLAN = PLAN
