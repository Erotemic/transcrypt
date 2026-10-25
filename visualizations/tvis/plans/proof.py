"""How genuine source-derived refinement is constructed and scoped."""
from tvis.diagram import Processing, Beat,Diagram,Link
from tvis.plans.common import carry_knowledge, mark, info4,row4,route

nodes=row4((
    ('rust','Production Rust','v3-core source', 'broker','code'),
    ('hax','Charon / Aeneas','tracked Lean extraction', 'assumed','filter'),
    ('spec','Independent spec','V3Wire / V3Policy', 'policy','document'),
    ('lean','Lean theorems','WP.spec against spec', 'proved','proof'),
))
nodes=mark(nodes,
    hax=('trusted-platform','A3','Pinned toolchain; translation soundness assumed'),
    lean=('source-proof','encode_file_header_refines','Example codec theorem; open has extra Realizes premise'),
)
links=(route(nodes,'rust','hax','translate','semantic translation','broker'),
       Link('model','hax','lean','generated functions',((-0.44,1.63),(3.93,1.63)),
            'proved',label_xy=(1.75,2.11)),
       route(nodes,'spec','lean','compare','independent model','policy'))
# Override the extraction->Lean arrow to run above the spec node. The final endpoint
# is the *right* edge of Lean; the spec->Lean arrow points rightward.
# Distinct routes keep the entire proof boundary visible in SVG.
links=(links[0],Link('model','hax','lean','RustM functions',((-0.44,1.86),(0.10,2.35),(3.86,2.35),(3.93,1.86)),
                    'proved',label_xy=(1.75,2.54)),
       route(nodes,'spec','lean','compare','spec proposition','policy'))
PLAN=Diagram(
    key='proof',title='Where the mathematical guarantee begins',
    kicker='Production Rust -> pinned Aeneas -> Lean theorem -> independent specification.',
    nodes=nodes,links=links,beats=(
        Beat('source', 'The actual no_std Rust core implements the serializer, parser, and security decisions.',
             nodes=tuple(n.key for n in nodes),status='implemented',
             knowledge=info4(nodes,(('transcrypt-v3-core','invoked by executable'),
                                  ('not hand-written model','source hash pinned'),
                                  ('wire shapes','auth and path policy'),
                                  ('theorem about RustM','compiled by Lean')))),
        Beat('translate', 'Pinned cargo-hax translates production functions; its semantic correctness is assumption A3.',
             links=('translate',),packet='translate',packet_label='Rust source',status='assumed',packet_kind='metadata',
             processing=Processing('hax','production Rust','RustM translation','metadata','metadata')),
        Beat('two_sides', 'The independent spec and translated Rust definitions meet in an actual refinement theorem.',
             links=('model','compare'),packet='compare',packet_label='expected behavior',status='proved',packet_kind='metadata',
             processing=Processing('lean','RustM + spec','Lean theorem','metadata','decision')),
        Beat('theorem', 'A compiled theorem means every permitted input satisfies its exact proposition, not just tests.',
             focus=('lean',),status='proved'),
        Beat('scope', 'The theorem is conditional on Realizes and model premises; it does not verify Git or AES internals.',
             focus=('spec',),status='assumed'),
    ),footer='Example anchors: encode_file_header_refines, open_record_spec, parse_file_header_spec; see PROOF-STATUS.md.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
