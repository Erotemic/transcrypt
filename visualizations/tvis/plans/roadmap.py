from dataclasses import replace

"""Remaining assurance work, rather than already-shipped UX features."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

nodes=row4((
    ('adapter','A4 input contracts','Git frame / move / key','assumed','git'),
    ('crypto','External review R-01','P6 release blocker','assumed','key'),
    ('remote','Optional remote audit','A13: deploy where needed','provider','cloud'),
    ('maintain','Proof maintenance','extract + rebuild in CI','proved','proof'),
))
nodes=mark(nodes,
    adapter=('planned','A4','Next: source-derived pure input checks'),
    crypto=('planned','R-01','Independent crypto and adapter review outstanding'),
    remote=('trusted-platform','A13','Remote enforcement only when operators deploy it'),
    maintain=('tested','W-00','Tracked CI extraction and build are implemented'),
)
links=(route(nodes,'adapter','crypto','review','reduce assumptions','assumed'),
       replace(route(nodes,'crypto','remote','deploy','optional','assumed'), dashed=True),
       replace(route(nodes,'remote','maintain','regress','CI loop','broker'), dashed=True))
PLAN=Diagram(
    key='roadmap',title='What remains to shrink the trusted boundary',
    kicker='Arbitrary patterns, stored-key unlock, rebind and migration are already implemented in this snapshot.',
    nodes=nodes,links=links,beats=(
        Beat('intent','Next: narrow A4 input provenance and close the external R-01 review; optional remote audit depends on the operator.',
             nodes=tuple(n.key for n in nodes),status='planned',
             knowledge=info4(nodes,(('A4 input correspondence','cat-file / move / key'),
                                  ('R-01 still outstanding','A5/A9 review pending'),
                                  ('remote hook adoption','A13 optional deployment'),
                                  ('W-00 generated match','CI is active now')))),
        Beat('adapter','Prove more pure cat-file response framing and decision inputs; do not claim a Lean proof of Unix filesystem writes.',
             links=('review',),packet='review',packet_label='adapter evidence',status='planned',
             processing=Processing('adapter','tested adapter','proof target','metadata','decision')),
        Beat('crypto','R-01 remains open: independent review of RustCrypto realization and high-consequence adapter paths.',
             links=('deploy',),packet='deploy',packet_label='crypto evidence',status='planned',
             processing=Processing('crypto','test vectors','review evidence','metadata','decision')),
        Beat('remote','A13 is optional remote audit deployment; it is a platform condition, not a missing local source-derived theorem.',
             links=('regress',),packet='regress',packet_label='deployment status',status='assumed',
             processing=Processing('remote','optional hook','deployment state','metadata','decision')),
        Beat('proofs','On each future core change, keep pinned extraction and the relevant Lean theorems in CI.',
             focus=('maintain',),status='implemented',
             processing=Processing('maintain','Rust source diff','tracked proofs','metadata','decision')),
    ),footer='Already delivered P0-P5. Next: A4 narrowing and P6/R-01. A13 remains an optional operator condition.')
PLAN=carry_knowledge(PLAN)
