"""Actual encrypt-on-Git-add path, with explicit implementation/assumption split."""
from tvis.diagram import Processing, Beat, Diagram
from tvis.plans.common import carry_knowledge, mark, info4, route, row4

nodes = row4((
    ('editor', 'Editor / disk', 'account.secret plaintext', 'guest', 'document'),
    ('filter', 'Git clean filter', 'native Rust adapter', 'broker', 'filter'),
    ('core', 'v3 protocol core', 'seal + validation', 'proved', 'shield'),
    ('git', 'Git index / remote', 'record is public', 'provider', 'git'),
))
nodes=mark(nodes,
    filter=('tested', 'A4', 'Real Git filter adapter; no complete Lean extraction'),
    core=('conditional-proof', 'seal_record_spec', 'Requires Realizes(A5), plus translator A3'),
    git=('trusted-platform', 'A7', 'Git index and object semantics'),
)
links = (route(nodes, 'editor', 'filter', 'source', 'file content', 'guest'),
         route(nodes, 'filter', 'core', 'request', 'config + path', 'broker'),
         route(nodes, 'core', 'git', 'sealed', 'authenticated record', 'proved'))
PLAN=Diagram(
    key='clean', title='git add: plaintext goes in; ciphertext goes out',
    kicker='The same file stays plaintext in the unlocked local checkout.',
    nodes=nodes, links=links, beats=(
        Beat('local', 'The developer edits ordinary plaintext; selection and filter installation are Git responsibilities.',
             nodes=tuple(n.key for n in nodes), status='implemented',
             knowledge=info4(nodes, (('account.secret', 'value = fake-example'),
                                  ('file bytes + path', 'effective filter'),
                                  ('no authority over Git', 'checks protocol gates'),
                                  ('no new object yet',)))),
        Beat('clean', 'Git sends bytes through the installed clean filter; it must pass the exact pathname.',
             links=('source',), packet='source', packet_label='plaintext bytes', status='assumed', packet_kind='plaintext',
             processing=Processing('filter', 'file + path', 'seal request', 'plaintext', 'metadata')),
        Beat('decide', 'seal_record is source-derived proved IF Realizes; RustCrypto performs the actual AES-SIV call.',
             links=('request',), packet='request', packet_label='path + config', status='proved', packet_kind='plaintext',
             processing=Processing('core', 'plaintext + AD', 'v3 record', 'plaintext', 'ciphertext'),
             knowledge=info4(nodes, (('still plaintext',),
                                  ('calls seal_record', 'and crypto adapter'),
                                  ('MaySeal preconditions', 'format / AD contract'),
                                  ('awaits ciphertext',)))),
        Beat('commit', 'Git stages the authenticated v3 record, not the plaintext processed by the filter.',
             links=('sealed',), packet='sealed', packet_label='v3 envelope', status='assumed', packet_kind='ciphertext',
             processing=Processing('git', 'v3 record', 'staged object', 'ciphertext', 'ciphertext'),
             knowledge=info4(nodes, (('plaintext remains local',),
                                  ('clean filter completes',),
                                  ('record = header + tag', 'and encrypted bytes'),
                                  ('Git stores record bytes', 'can be copied publicly')))),
    ), footer='Lean covers core decisions; complete Git filter invocation and RustCrypto behavior remain assumptions.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
