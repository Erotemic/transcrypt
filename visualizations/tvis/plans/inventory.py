"""Named proof inventory: which production functions, versus which models."""
from tvis.diagram import Processing, Beat, Diagram
from tvis.plans.common import carry_knowledge, mark, info4, row4

nodes = row4((
    ('codec', 'Wire codec', 'ACTUAL RUST: PROVED', 'proved', 'code'),
    ('checks', 'Parsers + gates', 'ACTUAL RUST: PROVED', 'proved', 'shield'),
    ('crypto', 'Seal / open', 'PROVED IF Realizes', 'proved', 'key'),
    ('lifecycle', 'Git lifecycle', 'LEAN MODEL PROVED', 'policy', 'git'),
))

nodes=mark(nodes,
    codec=('source-proof', 'encode_file_header_refines', 'Actual Rust serializer'),
    checks=('source-proof', 'parse_attr_response_spec', 'Source-derived selection/parse gate'),
    crypto=('conditional-proof', 'seal_record_spec', 'Only IF external Realizes'),
    lifecycle=('model-proof', 'hydratePlan_spec', 'Lean-defined sequencing model only'),
)

PLAN = Diagram(
    key='inventory', title='What exactly has a Lean theorem?',
    kicker='Three source-derived groups, one model group; no claim that the entire binary is proved.',
    nodes=nodes, links=(), beats=(
        Beat('codec', 'ACTUAL Rust codecs: every byte of the 55-byte config and 22-byte header matches the independent spec. Both public parsers classify invalid length and magic.',
             nodes=tuple(n.key for n in nodes), focus=('codec',), status='proved',
             knowledge=info4(nodes, (
                ('encode_config_refines', 'encode_file_header_refines', 'parse_config_spec', 'parse_file_header_spec'),
                ('Canonical path theorem', 'parse_index_entry_spec', 'decode_pkt_len_spec'),
                ('seal_record_spec', 'open_record_spec', 'requires Realizes (A5)'),
                ('hydratePlan_spec (MODEL)', 'lockEntry_spec (MODEL)', 'verifyPlan_spec (MODEL)'),
             ))),
        Beat('checks', 'ACTUAL Rust decisions: canonical Git paths, staged Git index records, object IDs, attribute replies, packet/frame headers and agent authorization.',
             focus=('checks',), status='proved'),
        Beat('crypto', 'ACTUAL Rust protocol functions: config authentication, seal and open conform to Lean specs for all admitted inputs, CONDITIONAL on an external cryptographic contract.',
             focus=('crypto',), status='proved'),
        Beat('models', 'MODEL ONLY: hydratePlan, lockEntry, verifyPlan and cleanModel describe intended Git sequencing. The effectful Rust Git/Unix adapter is not source-derived in these proofs.',
             focus=('lifecycle',), status='modeled'),
    ), footer='Full theorem-to-function inventory: proofs/aeneas/v3/PROOF-STATUS.md; boundary: V3-ASSUMPTIONS.md.')
PLAN = carry_knowledge(PLAN)
