"""Clone, unlock, authenticated smudge/hydrate, plaintext checkout."""
from tvis.diagram import Processing, Beat, Diagram
from tvis.plans.common import carry_knowledge, mark, info3,route,row3

nodes=row3((
    ('repo','Public clone','ciphertext in Git', 'provider','cloud'),
    ('check','v3 open_record','core + crypto adapter', 'proved','shield'),
    ('disk','Worktree writer','native plaintext write','guest','laptop'),
))
nodes=mark(nodes,
    check=('conditional-proof', 'open_record_spec', 'Requires Realizes(A5) for source-derived opening'),
    disk=('tested', 'A4', 'Native publish: A4 / A8; model theorem is separate'),
)
links=(route(nodes,'repo','check','cipher','record + expected path','provider'),
       route(nodes,'check','disk','release','authenticated plaintext','proved'))
PLAN=Diagram(
    key='clone',title='Clone and unlock: the same file becomes useful',
    kicker='The remote stays encrypted while the unlocked checkout contains ordinary plaintext.',
    nodes=nodes,links=links,beats=(
        Beat('clone', 'A new clone has only the Git record; without credentials, it cannot decrypt it.',
             nodes=tuple(n.key for n in nodes),status='implemented',
             knowledge=info3(nodes,(('encrypted Git object','committed config'),
                                  ('no authenticated key yet','cannot open record'),
                                  ('encrypted checkout','no usable plaintext')))),
        Beat('unlock', 'The current default unlock derives and stores a local key; --private uses the memory agent.',
             links=('cipher',),packet='cipher',packet_label='sealed blob',status='implemented', packet_kind='ciphertext',
             knowledge=info3(nodes,(('ciphertext unchanged',),
                                  ('stored key by default','or optional private agent'),
                                  ('developer supplied passphrase',)))),
        Beat('verify', 'The core demands an authentic record under the config and exact path before success.',
             focus=('check',),status='proved',
             processing=Processing('check','record + path','accept / refuse','ciphertext','decision')),
        Beat('hydrate', 'Native Git/OS code writes the opened bytes locally; those side effects are tested, not proved.',
             links=('release',),packet='release',packet_label='plaintext bytes',status='assumed', packet_kind='plaintext',
             processing=Processing('disk','authenticated bytes','local plaintext','plaintext','plaintext'),
             knowledge=info3(nodes,(('same ciphertext remains','available to the public'),
                                  ('authenticated opening','under Realizes'),
                                  ('account.secret plaintext','normal editor workflow')))),
    ),footer='Stored-key unlock is the default (A17); --private uses the optional memory agent (A6).')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
