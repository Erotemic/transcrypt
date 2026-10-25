"""Remaining assurance work, rather than already-shipped UX features."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

nodes=row4((
    ('adapter','Adapter refinement','native Git / OS effects','assumed','git'),
    ('crypto','Crypto review','A5 / A9 / A10','assumed','key'),
    ('remote','Remote enforcement','installable server audit','provider','cloud'),
    ('maintain','Proof maintenance','extract + rebuild in CI','proved','proof'),
))
nodes=mark(nodes,
    adapter=('planned','A4','Future source-derived adapter correspondence'),
    crypto=('planned','A9','External cryptographic review planned'),
    remote=('planned','A13','Broader deployment verification planned'),
    maintain=('tested','W-00','Tracked CI extraction and build are implemented'),
)
links=(route(nodes,'adapter','crypto','review','reduce assumptions','assumed'),
       route(nodes,'crypto','remote','deploy','validated build','assumed'),
       route(nodes,'remote','maintain','regress','continuous coverage','broker'))
PLAN=Diagram(
    key='roadmap',title='What remains to shrink the trusted boundary',
    kicker='Arbitrary patterns, stored-key unlock, rebind and migration are already implemented in this snapshot.',
    nodes=nodes,links=links,beats=(
        Beat('intent','Future: verify more effectful adapter behavior against the already-proved core decisions.',
             nodes=tuple(n.key for n in nodes),status='planned',
             knowledge=info4(nodes,(('A4 source correspondence','real OS/Git effects'),
                                  ('RustCrypto audit','A5 and A9 reviewed'),
                                  ('remote hook adoption','A13 operator deployment'),
                                  ('W-00 generated match','CI is active now')))),
        Beat('adapter','Move tested Git/OS call order and stamp-checked writes into source-derived refinement.',
             links=('review',),packet='review',packet_label='adapter evidence',status='planned',
             processing=Processing('adapter','tested adapter','proof target','metadata','decision')),
        Beat('crypto','Review cryptographic implementation and its realization of the external contract.',
             links=('deploy',),packet='deploy',packet_label='crypto evidence',status='planned',
             processing=Processing('crypto','test vectors','review evidence','metadata','decision')),
        Beat('remote','Help operators verify remote hook/audit deployment; do not pretend a local tool controls remotes.',
             links=('regress',),packet='regress',packet_label='deployment status',status='planned',
             processing=Processing('remote','optional hook','verified setup','metadata','decision')),
        Beat('proofs','On each future core change, keep pinned extraction and the relevant Lean theorems in CI.',
             focus=('maintain',),status='implemented',
             processing=Processing('maintain','Rust source diff','tracked proofs','metadata','decision')),
    ),footer='Already delivered: patterns, default stored key, v2 migration, path-bound renames. Remaining: A4/A9/A13.')
PLAN=carry_knowledge(PLAN)
