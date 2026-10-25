"""Clone, unlock, authenticated smudge/hydrate, plaintext checkout."""
from tvis.diagram import Beat, Diagram
from tvis.plans.common import carry_knowledge, info3,route,row3

nodes=row3((
    ('repo','Public clone','ciphertext in Git', 'provider','cloud'),
    ('check','v3 open_record','core + crypto adapter', 'proved','shield'),
    ('disk','Local worktree','plaintext after unlock','guest','laptop'),
))
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
        Beat('unlock', 'The current prototype derives a key from the passphrase and holds it in a local memory agent.',
             links=('cipher',),packet='cipher',packet_label='sealed blob',status='implemented',
             knowledge=info3(nodes,(('ciphertext unchanged',),
                                  ('password -> Argon2id key','config authenticated'),
                                  ('developer supplied passphrase',)))),
        Beat('verify', 'The core demands an authentic record under the config and exact path before success.',
             focus=('check',),status='proved'),
        Beat('hydrate', 'Native Git/OS code writes the opened bytes locally; those side effects are tested, not proved.',
             links=('release',),packet='release',packet_label='plaintext bytes',status='assumed',
             knowledge=info3(nodes,(('same ciphertext remains','available to the public'),
                                  ('authenticated opening','under Realizes'),
                                  ('account.secret plaintext','normal editor workflow')))),
    ),footer='Planned persistent local unlock is a UX target, not the credential mode implemented in snapshot 861975a.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
