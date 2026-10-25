"""Rename requires rebinding authentication to the destination's exact Git path."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

nodes=row4((
    ('git','Git rename','old blob, new path','provider','git'),
    ('adapter','Staged-index adapter','HEAD source + local data','broker','filter'),
    ('decide','seal_action gate','Seal / Rebind / Refuse','proved','shield'),
    ('seal','seal_record at new path','v3 ciphertext for target','proved','lock'),
))
nodes=mark(nodes,
    git=('trusted-platform','A7','Git rename + staged/index behavior'),
    adapter=('tested','A18','Calls gates on correct old/new bytes: A4'),
    decide=('source-proof','seal_action_spec','Source-derived rename decision'),
    seal=('conditional-proof','seal_record_spec','Reseal under destination path IF Realizes'),
)
links=(route(nodes,'git','adapter','inspect','old blob + target','provider'),
       route(nodes,'adapter','decide','decide','authenticity + edits','broker'),
       route(nodes,'decide','seal','rebind','new path + plaintext','proved'))
PLAN=Diagram(
    key='rename',title='Rename: ciphertext must be rebound to its new path',
    kicker='Moving old bytes alone does not authenticate them at a different pathname.',
    nodes=nodes,links=links,beats=(
        Beat('move','A Git move may retain a record bound to the old path: this is not a valid destination record.',
             nodes=tuple(n.key for n in nodes),status='assumed',
             knowledge=info4(nodes,(('old-path object','new index pathname'),
                                  ('looks at HEAD and index','reads local bytes'),
                                  ('will choose action',),('no destination record yet',)))),
        Beat('inspect','The tested Rust adapter locates the old object and current worktree bytes, without trusting filenames as revisions.',
             links=('inspect',),packet='inspect',packet_label='old blob + new path',packet_kind='ciphertext',
             processing=Processing('adapter','staged + HEAD','evidence of move','metadata','decision'),status='tested'),
        Beat('choose','The source-derived seal_action gate can request Seal, Rebind or Refuse from explicit facts.',
             links=('decide',),packet='decide',packet_label='move decision inputs',packet_kind='decision',
             processing=Processing('decide','move + local flags','Seal / Rebind','metadata','decision'),status='proved'),
        Beat('rebind','The record must be authentically opened at its old path and resealed for its new path; otherwise refuse.',
             links=('rebind',),packet='rebind',packet_label='new path + plaintext',packet_kind='plaintext',
             processing=Processing('seal','plaintext + new path','new bound record','plaintext','ciphertext'),status='proved',
             knowledge=info4(nodes,(('index now points to','destination pathname'),
                                  ('real Git flow tested','call correspondence A4'),
                                  ('seal_action_spec',),('record bound to target','IF Realizes(A5)')))),
    ),footer='A18: decision is source-derived proved; real Git rename detection is tested, not proved end-to-end.')
PLAN=carry_knowledge(PLAN)
