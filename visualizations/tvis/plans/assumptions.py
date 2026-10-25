"""Draw the trust boundary without painting the whole service green."""
from tvis.diagram import Processing, Beat, Diagram
from tvis.plans.common import carry_knowledge, mark, info4, route, row4

nodes = row4((
    ('core', 'v3 Rust core', 'A1 / A2 proved', 'proved', 'proof'),
    ('crypto', 'RustCrypto', 'A5 / A9 / A10', 'assumed', 'key'),
    ('adapter', 'Git + Unix adapter', 'A4 / A7 / A8', 'assumed', 'git'),
    ('remote', 'Remote / CI audit', 'A13 / A14', 'provider', 'cloud'),
))
nodes=mark(nodes,
    core=('source-proof','is_canonical_protected_path_spec','Pure policy core example'),
    crypto=('trusted-crypto','A5','RustCrypto / Realizes / A9 / A10'),
    adapter=('tested','A4','Adapter to core unproved; reviewed + real tests'),
    remote=('trusted-platform','A13','Deployment is optional/external'),
)
links=(route(nodes,'core','crypto','call','primitive contract','proved'),
       route(nodes,'crypto','adapter','operate','bytes + results','assumed'),
       route(nodes,'adapter','remote','publish','push commits','assumed'))
PLAN=Diagram(
    key='assumptions',title='Green is not a magic border around the app',
    kicker='Theorem, test, assumption and deployment condition are different evidence levels.',
    nodes=nodes,links=links,beats=(
        Beat('core', 'A1 and A2: the actual extracted codec and protocol decision core refine the independent spec.',
             nodes=tuple(n.key for n in nodes),status='proved',
             knowledge=info4(nodes,(('source-derived Lean','function contracts'),
                                  ('AES-SIV security','Argon2id + SHA-256'),
                                  ('Git subprocesses','filesystem effects'),
                                  ('remote policy','not automatic')))),
        Beat('crypto', 'A5/A9/A10: the RustCrypto instance must realize the abstract primitive contract.',
             links=('call',),packet='call',packet_label='SIV + AD',status='assumed',packet_kind='key',
             processing=Processing('crypto','AD + key + bytes','SIV tag / bytes','key','ciphertext')),
        Beat('adapter', 'A4/A7/A8: effectful Rust, Git selection, and filesystem behavior remain outside that proof.',
             links=('operate',),packet='operate',packet_label='Git / OS effects',status='assumed',packet_kind='metadata',
             processing=Processing('adapter','core result','Git / OS effect','decision','metadata')),
        Beat('remote', 'A13: history audit protects remotes only where deployed; A14: keyless envelope checks are not authentication.',
             links=('publish',),packet='publish',packet_label='commits',status='assumed',packet_kind='ciphertext',
             processing=Processing('remote','commit','audit / bypass','ciphertext','decision')),
    ),footer='See V3-ASSUMPTIONS.md for each premise, evidence level, residual risk, and next reduction.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
