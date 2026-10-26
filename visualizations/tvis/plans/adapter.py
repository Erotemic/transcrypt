"""Concrete A4 adapter-correspondence debts, deliberately separated from proofs."""
from dataclasses import replace

from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

def overhead(nodes, origin, destination, key, label, role):
    """Route moving packets above wide node cards so labels never cover the gates."""
    basic = route(nodes, origin, destination, key, label, role)
    a, b = basic.path[0], basic.path[-1]
    upper = 2.43
    return replace(basic,
                   path=((a[0], 2.01), (a[0]+.24, upper),
                         (b[0]-.24, upper), (b[0], 2.01)),
                   label_xy=((a[0]+b[0])/2, 2.65))


nodes = row4((
    ('git', 'Git attribute + OID', 'A7 / A19 external', 'provider', 'git'),
    ('parser', 'Proved byte parser', 'exact raw paths', 'proved', 'shield'),
    ('adapter', 'Effectful Rust adapter', 'A4: inputs / call order', 'broker', 'code'),
    ('gate', 'Proved action gate', 'seal_action_spec', 'proved', 'proof'),
))
nodes = mark(nodes,
    git=('trusted-platform', 'A7/A19', 'Git supplies matching and object bytes'),
    parser=('source-proof', 'parse_attr_response_spec',
            'Source-derived exact NUL-delimited response parser'),
    adapter=('tested', 'A4',
             'cat-file framing, move provenance, stored-key selection still tested'),
    gate=('source-proof', 'seal_action_spec',
          'Decision is proved for facts supplied; provenance of facts is A4'),
)
links = (
    overhead(nodes, 'git', 'parser', 'reply', 'NUL', 'provider'),
    overhead(nodes, 'parser', 'adapter', 'flags', 'paths', 'proved'),
    overhead(nodes, 'adapter', 'gate', 'facts', 'facts', 'broker'),
)
PLAN = Diagram(
    key='adapter',
    title='A4: where the real adapter must match the proof',
    kicker='A proved decision cannot establish the truth of facts supplied by its unproved caller.',
    nodes=nodes, links=links, beats=(
        Beat('selection',
             'Git matches .gitattributes rules under A7/A19. Git matching itself is not a Lean theorem.',
             nodes=tuple(n.key for n in nodes), status='assumed',
             knowledge=info4(nodes, (
                 ('raw Git paths', 'NUL attribute reply'),
                 ('parse_attr_response_spec', 'completeness proved'),
                 ('request built natively', 'same input bytes? A4'),
                 ('seal_action_spec', 'expects correct facts'),
             ))),
        Beat('parsing',
             'parse_attr_response_spec and parse_attr_response_complete prove exact answer parsing, not Git selection or request construction.',
             links=('reply',), packet='reply', packet_label='NUL',
             packet_kind='metadata', status='proved',
             processing=Processing('parser', 'request + NUL reply',
                                   'selected flags', 'metadata', 'decision')),
        Beat('object',
             'is_object_id_spec proves hexadecimal OID syntax; the cat-file --batch response header and consumption remain native A4/A7 checks.',
             links=('flags',), packet='flags', packet_label='paths',
             packet_kind='path', status='tested',
             processing=Processing('adapter', 'OID + cat-file bytes',
                                   'record snapshot', 'metadata', 'ciphertext'),
             knowledge=info4(nodes, (
                 ('index snapshot + OIDs', 'A7 object lookup'),
                 ('is_object_id_spec', 'OID syntax is proved'),
                 ('cat-file frame check', 'A4: native / tested'),
                 ('still needs correct', 'authenticated input'),
             ))),
        Beat('provenance',
             'For rename repair, the adapter computes local_change and moved. These input facts are reviewed/tested; they are not proved by seal_action_spec.',
             focus=('adapter',), status='tested',
             processing=Processing('adapter', 'Git index + old path',
                                   'local_change / moved', 'metadata', 'decision'),
             knowledge=info4(nodes, (
                 ('Git history and staged', 'index state A7'),
                 ('path policy proved', 'not Git matching'),
                 ('local_change / moved', 'A4 / A18 tested'),
                 ('seal / rebind / keep', 'decision yet to run'),
             ))),
        Beat('decision',
             'seal_action_spec proves Seal, Rebind, Keep or Refuse for the supplied inputs. It does not prove that a Git rename was detected correctly.',
             links=('facts',), packet='facts', packet_label='facts',
             packet_kind='decision', focus=('gate',), status='proved',
             processing=Processing('gate', 'authenticated + local facts',
                                   'seal / rebind / refuse', 'metadata', 'decision')),
        Beat('credential',
             'Stored derived-key selection is implemented and tested (A17); authenticate_config_spec is conditional on Realizes, not a proof of the file read.',
             focus=('adapter',), status='tested',
             processing=Processing('adapter', 'key file + config',
                                   'candidate key', 'key', 'key')),
        Beat('effects',
             'Stamp-checked rename, fsync and publication are tested A8/A12. The lifecycle model is proved, but production Git/OS effects are not.',
             focus=('adapter',), status='tested',
             processing=Processing('adapter', 'approved action',
                                   'OS / Git side effect', 'decision', 'metadata')),
        Beat('target',
             'Next narrow A4 by extracting pure cat-file frame checks and rebind/key-load input decisions. Keep Git, filesystem and cryptographic libraries explicit contracts.',
             focus=('adapter',), status='planned',
             processing=Processing('adapter', 'tested checks',
                                   'candidate pure core', 'metadata', 'decision')),
    ),
    footer='Remaining A4 debt: trusted inputs and native effects, not an undiscovered hole in seal_action_spec.',
)
PLAN = carry_knowledge(PLAN)
