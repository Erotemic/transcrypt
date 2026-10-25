"""Explain the intended threat model and permitted disclosures."""
from tvis.diagram import Beat,Diagram
from tvis.plans.common import carry_knowledge, info3,route,row3
nodes=row3((
    ('developer','Unlocked developer','plaintext + local key', 'guest','laptop'),
    ('remote','Public Git history','v3 objects + metadata', 'provider','cloud'),
    ('observer','Offline observer','no derived key', 'assumed','warning'),
))
links=(route(nodes,'developer','remote','push','authenticated blob','broker'),
       route(nodes,'remote','observer','read','entire public history','provider'))
PLAN=Diagram(
    key='offline',title='What security means for a public repository',
    kicker='The threat is an offline reader of public history, not the owner of an unlocked workstation.',
    nodes=nodes,links=links,beats=(
        Beat('local', 'The developer keeps plaintext locally by design. Local-at-rest secrecy is not the default promise.',
             nodes=tuple(n.key for n in nodes),status='explainer',
             knowledge=info3(nodes,(('secret contents','local derived key'),
                                  ('committed ciphertext','record lengths, paths'),
                                  ('public repo access','no key material')))),
        Beat('public', 'Git history exposes ciphertext, pathnames, change timing, lengths and deterministic equality.',
             links=('push','read'),packet='read',packet_label='public Git bytes',status='implemented'),
        Beat('offline', 'Argon2id slows passphrase guesses; entropy of the passphrase still determines offline resistance.',
             focus=('observer',),status='assumed',
             knowledge=info3(nodes,(('chooses strong passphrase',),
                                  ('public salt + auth tag',),
                                  ('can run offline guesses','may compare revisions','cannot see local key')))),
        Beat('limits', 'Old plaintext commits and rollback remain observable; v3 cannot erase Git history.',
             focus=('remote',),status='assumed'),
    ),footer='No at-rest encryption claim. No rollback resistance. Deterministic encryption intentionally leaks equality.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
