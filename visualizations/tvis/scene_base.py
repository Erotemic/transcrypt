"""Manim animation of the same editable protocol beats used by SVG previews.

Scene authors can override ``construct`` and call ``draw_plan`` or ordinary
Manim methods. Heavy Manim imports are isolated here, not in pure plans.
"""
from __future__ import annotations

import os
from manim import (Circumscribe, Create, FadeIn, FadeOut, MoveAlongPath,
                   RoundedRectangle, Scene, Text, VGroup, DOWN, UP)

from tvis.components.graphics import (
    edge_group, knowledge_card, link_path, node_card, package_group, processing_card,
    region_box, text_label, traveling_label, xy,
)
from tvis.diagram import Diagram, EVIDENCE_ROLES, layer_geometry, validate
from tvis.palette import palette


class DiagramScene(Scene):
    PLAN: Diagram

    def construct(self) -> None:
        self.draw_plan()

    def draw_plan(self) -> None:
        plan=self.PLAN
        validate(plan)
        colors=palette(os.environ.get('TVIS_THEME','dark'))
        speed=float(os.environ.get('TVIS_SPEED','1.0'))
        if not 0.1 <= speed <= 10:
            raise ValueError('TVIS_SPEED must be in [0.1,10]')
        self.camera.background_color=colors['background']
        title=text_label(plan.title,colors,font_size=36)
        title.move_to(xy((-1.0,3.36)))
        # Fit the subtitle between the frame's left edge and the status badge.
        kicker=text_label(plan.kicker,colors,font_size=16,color='muted',max_width=11.0)
        kicker.move_to(xy((-1.0,2.9)))
        footer=text_label(plan.footer,colors,font_size=12,color='muted')
        footer.move_to(xy((0,-3.85)))
        self.add(*(region_box(reg,colors) for reg in plan.regions))
        self.play(FadeIn(title),FadeIn(kicker),FadeIn(footer),run_time=0.52/speed)
        cards={node.key:node_card(node,colors) for node in plan.nodes}
        routes={link.key:edge_group(link,colors) for link in plan.links}
        packages={item.key:package_group(item,colors) for item in plan.packages}
        node_map=plan.node_map()
        link_map=plan.link_map()
        shown_nodes:set[str]=set()
        shown_links:set[str]=set()
        shown_packages:set[str]=set()
        shown_layers:set[str]=set()
        knowledge_group=VGroup()
        label_panel=RoundedRectangle(width=13.05,height=0.85,
                                     corner_radius=0.14,
                                     fill_color=colors['surface_soft'],fill_opacity=1,
                                     stroke_color=colors['neutral'],stroke_width=0.6)
        label_panel.move_to(xy((0,-3.2)))
        self.add(label_panel)
        prev_caption=None
        prev_status=None
        prev_processing=None
        for beat_index, stage in enumerate(plan.beats):
            self.next_section(stage.key)
            motion=[Create(routes[k]) for k in stage.links if k not in shown_links]
            motion += [FadeIn(cards[k],shift=UP*0.04) for k in stage.nodes if k not in shown_nodes]
            for pk in plan.visible_packages(beat_index):
                count=plan.visible_layer_depth(pk.key,beat_index)+1
                for layer_index,(layer,*_) in enumerate(layer_geometry(pk)[:count]):
                    if layer.key not in shown_layers:
                        motion.append(FadeIn(packages[pk.key][layer_index]))
                        shown_layers.add(layer.key)
            shown_nodes.update(stage.nodes)
            shown_links.update(stage.links)
            shown_packages.update(stage.packages)
            if motion:
                self.play(*motion,run_time=stage.duration/speed)
            caption=text_label(stage.caption,colors,font_size=19,max_width=12.25)
            caption.move_to(label_panel.get_center())
            status_text={'explainer':'EXPLANATION','implemented':'IN CODE',
                         'proved':'SOURCE-DERIVED PROOF','modeled':'MODEL PROOF',
                         'tested':'TESTED','assumed':'TRUSTED PREMISE',
                         'planned':'DESIGN GOAL','open':'NOT YET PROVEN'}[stage.status]
            status_role={'proved':'proved','modeled':'policy','tested':'broker',
                         'assumed':'assumed','planned':'open','open':'open'}.get(stage.status,'policy')
            status=Text(status_text,font_size=14,color=colors[status_role],weight='BOLD')
            status.move_to(xy((5.6,3.28)))
            old=[FadeOut(x) for x in (prev_caption,prev_status) if x is not None]
            self.play(*old,FadeIn(caption),FadeIn(status),run_time=0.3/speed)
            prev_caption,prev_status=caption,status
            # Every beat's knowledge list is a *complete replacement*.
            new_knowledge=VGroup(*(knowledge_card(k,node_map[k.owner],colors)
                                   for k in stage.knowledge))
            if len(knowledge_group) or len(new_knowledge):
                animations=[]
                if len(knowledge_group):
                    animations.append(FadeOut(knowledge_group))
                if len(new_knowledge):
                    animations.append(FadeIn(new_knowledge))
                if animations:
                    self.play(*animations,run_time=0.37/speed)
            knowledge_group=new_knowledge
            if prev_processing is not None:
                self.play(FadeOut(prev_processing),run_time=0.15/speed)
                prev_processing=None
            if stage.processing:
                step=stage.processing
                card=processing_card(step,node_map[step.node],colors)
                self.play(FadeIn(card[0]),FadeIn(card[1]),run_time=0.28/speed)
                self.play(FadeIn(card[2]),FadeIn(card[3]),run_time=0.38/speed)
                prev_processing=card
            if stage.packet:
                route=link_map[stage.packet]
                track=link_path(route)
                marker=traveling_label(stage.packet_label,stage.packet_kind,colors)
                marker.move_to(track.get_start())
                self.add(marker)
                self.play(MoveAlongPath(marker,track),run_time=max(0.7,stage.duration)/speed)
                self.remove(marker)
            for target in stage.focus:
                item=cards.get(target) or routes.get(target)
                if item is not None:
                    self.play(Circumscribe(item,color=(colors[EVIDENCE_ROLES[node_map[target].evidence.level]]
                                                       if target in node_map and node_map[target].evidence
                                                       else colors['policy']),fade_out=True,
                                           time_width=0.45),run_time=0.4/speed)
            if stage.layer_focus:
                for name in shown_packages:
                    for j, (layer, *_rest) in enumerate(layer_geometry(plan.package_map()[name])):
                        if layer.key==stage.layer_focus and layer.key in shown_layers:
                            self.play(Circumscribe(packages[name][j],color=colors['policy'],
                                                   fade_out=True,time_width=0.5),
                                      run_time=0.55/speed)
            self.wait(stage.hold/speed)
