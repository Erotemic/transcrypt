"""Manim entrypoint. Edit plans/legend.py to change scene geometry."""
from tvis.scene_base import DiagramScene
from tvis.plans.legend import PLAN

class VisualLegend(DiagramScene):
    PLAN = PLAN
