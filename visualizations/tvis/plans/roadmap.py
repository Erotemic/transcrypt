"""Future UX improvements classified as intentions, never retroactive proof facts."""
from tvis.diagram import Beat,Diagram
from tvis.plans.common import carry_knowledge, info4,route,row4

nodes=row4((
    ('policy','Select any files','native Git attributes', 'policy','path'),
    ('unlock','Unlock once','persistent local key', 'guest','key'),
    ('migrate','Transition from v2','one-time migration', 'broker','git'),
    ('proof','Keep proofs current','Rust -> Aeneas -> Lean', 'proved','proof'),
))
links=(route(nodes,'policy','unlock','choose','explicit policy', 'policy'),
       route(nodes,'unlock','migrate','import','controlled transition','broker'),
       route(nodes,'migrate','proof','verify','v3 semantics','proved'))
PLAN=Diagram(
    key='roadmap',title='The destination: secure Git that feels like Git',
    kicker='This is the design goal, not a claim that all listed features are implemented.',
    nodes=nodes,links=links,beats=(
        Beat('intent', 'The developer chooses arbitrary paths through Git attributes, not a hardcoded suffix.',
             nodes=tuple(n.key for n in nodes),status='planned',
             knowledge=info4(nodes,(('config/private/**','.env.production'),
                                  ('unlock once','then normal work'),
                                  ('one-time v2 -> v3','not old crypto in core'),
                                  ('source-derived proof','regression CI')))),
        Beat('credentials', 'Default to persistent local unlock; optional memory-only mode uses the identical v3 wire format.',
             links=('choose',),packet='choose',packet_label='local policy',status='planned'),
        Beat('transition', 'A recoverable transition path matters; ongoing legacy ciphertext support does not.',
             links=('import',),packet='import',packet_label='migration',status='planned'),
        Beat('maintenance', 'Every security-critical core change must rebuild the extracted Lean proof and assumption ledger.',
             links=('verify',),packet='verify',packet_label='fresh proof',status='planned'),
    ),footer='Formalize the real public-history guarantee, not every possible restriction on the user\'s local machine.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
