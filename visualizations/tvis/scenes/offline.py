"""Manim entrypoint. Edit plans/offline.py to change scene geometry."""
from tvis.scene_base import DiagramScene
from tvis.plans.offline import PLAN

class OfflineThreatModel(DiagramScene):
    PLAN = PLAN
