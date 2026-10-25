"""Visual grammar: local / public / source-derived / trusted."""
from tvis.diagram import Processing, Beat, Diagram
from tvis.plans.common import carry_knowledge, mark, info4, route, row4

nodes = row4((
    ('local', 'Local checkout', 'ordinary plaintext', 'guest', 'laptop'),
    ('core', 'Verified Rust core', 'Aeneas + Lean', 'proved', 'proof'),
    ('adapter', 'Git / crypto calls', 'effectful boundary', 'assumed', 'git'),
    ('public', 'Public Git history', 'untrusted reader', 'provider', 'cloud'),
))
nodes=mark(nodes,
    core=('source-proof','is_canonical_protected_path_spec','Example unconditional policy theorem'),
    adapter=('tested','A4','Git / crypto / OS outside this theorem'),
)
links = (route(nodes, 'local', 'core', 'data', 'content bytes', 'guest'),
         route(nodes, 'core', 'adapter', 'effect', 'seal / open', 'proved'),
         route(nodes, 'adapter', 'public', 'commit', 'Git object', 'assumed'))
PLAN = Diagram(
    key='legend', title='One file; two worlds; one proof boundary',
    kicker='Data color describes bytes; the badge under each operation describes its evidence.',
    nodes=nodes, links=links, beats=(
        Beat('worlds', 'Your checkout is plaintext. The public repository should contain only ciphertext.',
             nodes=tuple(n.key for n in nodes), status='explainer',
             knowledge=info4(nodes, (('edits .secret files', 'knows plaintext'),
                                  ('gets bytes + context', 'decides validation'),
                                  ('Git and RustCrypto', 'execute side effects'),
                                  ('sees Git blobs', 'no private key')))),
        Beat('enter', 'Git runs a clean filter; local plaintext becomes input to the verified decision core.',
             links=('data',), packet='data', packet_label='plaintext',packet_kind='plaintext', status='implemented'),
        Beat('proved', 'Lean relates the extracted core functions to an independent wire and policy specification.',
             links=('effect',), focus=('core',), status='proved'),
        Beat('trust', 'The adapter and cryptographic libraries still perform the real effects under explicit assumptions.',
             links=('commit',), packet='commit', packet_label='v3 record',packet_kind='ciphertext', status='assumed'),
    ), footer='This is a teaching diagram, not a whole-program proof. Each later scene names its evidence.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
