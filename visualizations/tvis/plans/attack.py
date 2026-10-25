"""Three independent rejection examples: tamper, wrong path, wrong config."""
from tvis.diagram import Beat, Diagram
from tvis.plans.common import carry_knowledge, info3,route,row3

nodes=row3((
    ('attacker','Offline attacker','can copy/edit Git blobs','provider','warning'),
    ('core','Verified open gate','config + path + record','proved','shield'),
    ('checkout','Local checkout','only accepted plaintext','guest','laptop'),
))
links=(route(nodes,'attacker','core','attempt','substituted record','provider'),
       route(nodes,'core','checkout','release','only on success','proved'))
PLAN=Diagram(
    key='attack',title='What a forged or misplaced record cannot do',
    kicker='Successful open implies exactly authenticated bytes, conditional on the primitive contract.',
    nodes=nodes,links=links,beats=(
        Beat('modify', 'An attacker modifies a record, copies it from another path, or substitutes another config.',
             nodes=tuple(n.key for n in nodes),status='explainer',
             knowledge=info3(nodes,(('can edit public history','cannot supply the key'),
                                  ('expected config id','exact canonical Git path'),
                                  ('no new plaintext yet',)))),
        Beat('challenge', 'The verification gate checks authenticated data for the expected path and config.',
             links=('attempt',),packet='attempt',packet_label='modified blob',status='proved'),
        Beat('reject', 'Under AES-SIV authenticity, malicious modifications are rejected except with negligible forgery probability.',
             focus=('core',),status='assumed',
             knowledge=info3(nodes,(('cannot mint a valid tag','without key'),
                                  ('open_record returns error','buffer zeroing on auth fail'),
                                  ('no unauthenticated release',)))),
        Beat('genuine', 'A genuine record opens to exactly its authenticated plaintext; the adapter publishes those bytes.',
             links=('release',),packet='release',packet_label='valid plaintext',status='proved',
             knowledge=info3(nodes,(('still sees only blobs',),
                                  ('accepted genuine record','under Realizes'),
                                  ('receives exact authenticated','plaintext bytes')))),
    ),footer='Computational AES-SIV unforgeability is assumed (A10); a successful Lean theorem is not an AES security proof.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
