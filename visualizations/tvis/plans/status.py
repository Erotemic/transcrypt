"""Evidence-based completion snapshot of the *current* v3 roadmap.

These are not percentages of program verification: each node represents a
separate obligation, and every evidence badge has its own narrower scope.
"""
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
    ('core', 'Source-derived core', 'V2-V4 / A1-A2', 'proved', 'proof'),
    ('models', 'Lifecycle models', 'V5 / Lean sequencing', 'policy', 'shield'),
    ('product', 'Rust product tracks', 'P0-P5 complete', 'broker', 'code'),
    ('review', 'Release qualification', 'P6 / R-01 outstanding', 'open', 'document'),
))
nodes = mark(nodes,
    core=('source-proof', 'seal_action_spec',
          'Example proved Rust decision; protocol functions require Realizes'),
    models=('model-proof', 'hydratePlan_spec',
            'Lean plan theorem; real effectful adapter remains A4'),
    product=('tested', 'P0-P5',
             'Implemented and exercised; P5 completes core proofs, not A4'),
    review=('planned', 'R-01',
            'Independent crypto/adapter review is still a release gate'),
)
links = (
    overhead(nodes, 'core', 'models', 'contracts', 'core', 'proved'),
    overhead(nodes, 'models', 'product', 'realize', 'model', 'policy'),
    overhead(nodes, 'product', 'review', 'qualify', 'R-01', 'broker'),
)
PLAN = Diagram(
    key='status',
    title='Formal core achieved; release review outstanding',
    kicker='V0-V5 achieved; V6 internal done, external R-01 open; V7 Bash v3 deferred by policy.',
    nodes=nodes, links=links, beats=(
        Beat('roadmap',
             'V0-V5 are achieved in their documented scope. V6 internal checks exist, but external R-01 is outstanding. V7 Bash v3 is explicitly deferred.',
             nodes=tuple(n.key for n in nodes), status='explainer',
             knowledge=info4(nodes, (
                 ('V2 extraction pinned', 'V3 bytes exact', 'V4 decision proofs'),
                 ('V5 Lean sequence', 'adversarial real-Git tests'),
                 ('P0-P4 product', 'P5 core correspondence', 'all marked done'),
                 ('V6 internal reviewed', 'R-01 not complete', 'not release certified'),
             ))),
        Beat('core',
             'Production Rust encoders, parsers and pure decision gates have source-derived proofs; seal/open/authentication remain conditional on Realizes.',
             focus=('core',), status='proved',
             processing=Processing('core', 'extracted Rust + spec',
                                   'WP.spec theorem', 'metadata', 'decision')),
        Beat('models',
             'The hydrate, lock, verify and filter sequencing theorems are proved for Lean-defined models, not for the native Git/OS adapter.',
             links=('contracts',), packet='contracts', packet_label='core',
             packet_kind='decision', status='modeled',
             processing=Processing('models', 'core results',
                                   'modeled action plan', 'decision', 'decision')),
        Beat('product',
             'P0-P5 are complete in the active charter: adapter fixes, arbitrary attributes, stored-key unlock, Git workflows, v2 migration, and core proof correspondence.',
             links=('realize',), packet='realize', packet_label='model',
             packet_kind='metadata', status='tested',
             processing=Processing('product', 'model + real Git',
                                   'tested Rust behavior', 'metadata', 'decision'),
             knowledge=info4(nodes, (
                 ('A1/A2 core proved', 'A3 translator assumed'),
                 ('A4 effectful bridge', 'only model proved'),
                 ('P0-P5 implemented', 'P6 still outstanding'),
                 ('crypto review R-01', 'external, not complete'),
             ))),
        Beat('review',
             'P6 is not finished: independent R-01 cryptographic/adapter review is required. CI and internal review do not substitute for it.',
             links=('qualify',), packet='qualify', packet_label='R-01',
             packet_kind='metadata', focus=('review',), status='planned',
             processing=Processing('review', 'proofs + tests',
                                   'R-01 open', 'metadata', 'decision')),
    ),
    footer='Completion here is by roadmap scope, not a percentage of verified executable code.',
)
PLAN = carry_knowledge(PLAN)
