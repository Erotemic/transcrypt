"""Separate the proved protocol core from proved *models* of effectful sequencing."""
from tvis.diagram import Beat, Diagram
from tvis.plans.common import carry_knowledge, info4, route, row4

nodes=row4((
    ('staged','Git index snapshot','objects + raw paths', 'provider','git'),
    ('core','Verified open gate','actual production Rust', 'proved','shield'),
    ('model','Lean plan model','hydrate / lock / verify', 'policy','proof'),
    ('effect','Native file writes','OS side effects', 'assumed','database'),
))
links=(route(nodes,'staged','core','load','staged record','provider'),
       route(nodes,'core','model','reason','authenticated result','proved'),
       route(nodes,'model','effect','execute','operation plan','assumed'))
PLAN=Diagram(
    key='lifecycle',title='A proved plan is not a proved filesystem',
    kicker='The source-derived gate is green; the sequencing theorem is purple; real side effects remain amber.',
    nodes=nodes,links=links,beats=(
        Beat('objects','The adapter selects staged objects. Git and the object-id snapshot semantics are premises.',
             nodes=tuple(n.key for n in nodes),status='assumed',
             knowledge=info4(nodes,(('staged ciphertext','index path and OID'),
                                  ('authenticates a record','for this config/path'),
                                  ('models failure ordering','no side effects'),
                                  ('actual filesystem','not yet changed')))),
        Beat('open','The real production core accepts only an authenticated opening under the primitive contract.',
             links=('load',),packet='load',packet_label='record bytes',status='proved'),
        Beat('model','Lean proves that the model checks its preconditions before proposed writes.',
             links=('reason',),packet='reason',packet_label='approved result',status='modeled',
             knowledge=info4(nodes,(('immutable OIDs','assumed Git behavior'),
                                  ('verified open decision',),
                                  ('hydratePlan_spec','lockEntry_spec','verifyPlan_spec'),
                                  ('must follow the plan','A4 correspondence')))),
        Beat('effect','Actual rename, fsync, file stamps and agent I/O are tested but not fully extracted into Lean.',
             links=('execute',),packet='execute',packet_label='native operation',status='assumed'),
    ),footer='Proof boundary: generated core + model; assumption A4: real adapter follows it on the same bytes.')
PLAN=carry_knowledge(PLAN)
