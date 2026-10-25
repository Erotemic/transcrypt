"""The AES-SIV call is separate from the proved Rust envelope decisions."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info3, mark, route, row3

nodes=row3((
    ('gate','seal_record gate','Rust core checks inputs','proved','shield'),
    ('primitive','RustCrypto AES-SIV','tag + ciphertext bytes','assumed','key'),
    ('assemble','Rust core record','header + tag + body','proved','document'),
))
nodes=mark(nodes,
    gate=('conditional-proof','seal_record_spec','Source-derived seal IF Realizes(A5)'),
    primitive=('trusted-crypto','A5','Keyed Realizes tested, but not proved; A9/A10'),
    assemble=('source-proof','encode_file_header_refines','22-byte header layout; full record still conditional'),
)
links=(route(nodes,'gate','primitive','invoke','plaintext + AD components','secret'),
       route(nodes,'primitive','assemble','return','tag and encrypted body','guest'))
PLAN=Diagram(
    key='crypto',title='Sealing: what Lean proves vs what AES-SIV does',
    kicker='The right-hand stage is the same Rust core after the external crypto call returns.',
    nodes=nodes,links=links,beats=(
        Beat('gate','The core checks the size, canonical path, config and output buffer; seal_record_spec is conditional.',
             nodes=tuple(n.key for n in nodes),focus=('gate',),status='proved',
             processing=Processing('gate','file + path','seal request','plaintext','decision'),
             knowledge=info3(nodes,(('original plaintext','public config and path'),
                                  ('not invoked yet',),('no new record yet',)))),
        Beat('primitive','AES-SIV consumes plaintext, secret key and three distinct AD components: domain, config, path.',
             links=('invoke',),packet='invoke',packet_label='bytes + AD + key',packet_kind='plaintext',
             processing=Processing('primitive','plaintext + AD','tag + body','plaintext','ciphertext'),status='assumed',
             knowledge=info3(nodes,(('MaySeal preconditions','conditional theorem'),
                                  ('64-byte secret key','ordered AD components','actual AES-SIV call'),
                                  ('not yet serialized',)))),
        Beat('output','The external primitive returns ciphertext and tag; the core assembles the proved 22-byte header.',
             links=('return',),packet='return',packet_label='tag + ciphertext',packet_kind='ciphertext',
             processing=Processing('assemble','tag + body','v3 record','ciphertext','ciphertext'),status='proved',
             knowledge=info3(nodes,(('seal_record success','IF Realizes(A5)'),
                                  ('no Lean proof of AES','differentially tested'),
                                  ('22-byte header','16-byte SIV tag','encrypted content')))),
    ),footer='Header layout is source-proved; complete sealing is proved only IF Realizes; A10 security assumed.')
PLAN=carry_knowledge(PLAN)
