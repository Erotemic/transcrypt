"""Derive and authenticate the key before activating the current default unlock."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

nodes=row4((
    ('pass','Passphrase', 'local user input', 'secret', 'key'),
    ('kdf','Argon2id', 'RustCrypto KDF', 'assumed', 'key'),
    ('auth','Config auth gate', 'production Rust core', 'proved', 'shield'),
    ('store','Credential store', '.git/ local-only file', 'broker', 'vault'),
))
nodes=mark(nodes,
    kdf=('trusted-crypto','A9','Argon2id implementation and hardness A10'),
    auth=('conditional-proof','authenticate_config_spec','Source-derived theorem IF Realizes'),
    store=('tested','A17','Default stored-key lifetime; optional private agent'),
)
links=(route(nodes,'pass','kdf','derive','passphrase + salt','secret'),
       route(nodes,'kdf','auth','check','derived 64-byte key','policy'),
       route(nodes,'auth','store','activate','only if config authentic','proved'))
PLAN=Diagram(
    key='unlock',title='Unlock: passphrase to authenticated local key',
    kicker='Argon2id is trusted external crypto; the core checks the public config; native storage is tested.',
    nodes=nodes,links=links,beats=(
        Beat('input','The passphrase is entered locally; the repository config provides a public salt.',
             nodes=tuple(n.key for n in nodes),status='implemented',
             knowledge=info4(nodes,(('user knows passphrase','not sent to remote'),
                                  ('public config salt','derivation settings'),
                                  ('on-disk public config','will check tag'),
                                  ('no key stored yet',)))),
        Beat('derive','Argon2id derives the 64-byte key; library correctness and hardness are outside Lean.',
             links=('derive',),packet='derive',packet_label='password + salt',packet_kind='key',
             processing=Processing('kdf','passphrase + salt','derived key','key','key'),status='assumed',
             knowledge=info4(nodes,(('plaintext password',),('Argon2id input',),
                                  ('candidate derived key','public config bytes'),('not activated yet',)))),
        Beat('authenticate','The source-derived authenticate_config gate rejects a mismatched key or config IF Realizes.',
             links=('check',),packet='check',packet_label='candidate key',packet_kind='key',
             processing=Processing('auth','key + config','Ok / refuse','key','decision'),status='proved'),
        Beat('persist','Only after authentication, the default mode stores the key in .git/transcrypt-v3/key.',
             links=('activate',),packet='activate',packet_label='authenticated key',packet_kind='key',
             processing=Processing('store','accepted key','local credential','key','key'),status='tested',
             knowledge=info4(nodes,(('passphrase not remote',),('key derivation finished',),
                                  ('config authenticated','under Realizes'),
                                  ('key in .git/','private mode: agent')))),
    ),footer='A17: stored-key mode is the default; --private uses a memory agent. Not disk encryption.')
PLAN=carry_knowledge(PLAN)
