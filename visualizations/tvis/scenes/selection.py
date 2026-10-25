"""Manim entrypoint. Edit plans/selection.py to change scene geometry."""
from tvis.scene_base import DiagramScene
from tvis.plans.selection import PLAN

class ProtectedSelection(DiagramScene):
    PLAN = PLAN
