"""Manim entrypoint for the audit operation storyboard."""
from tvis.scene_base import DiagramScene
from tvis.plans.audit import PLAN


class AuditDeploymentBoundary(DiagramScene):
    PLAN = PLAN
