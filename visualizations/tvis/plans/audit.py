"""Separate keyless envelope-shape proof from optional deployment of history audits."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

nodes=row4((
    ('git','Git commit tree','paths + object IDs','provider','git'),
    ('shape','Envelope check','keyless record shape','proved','shield'),
    ('audit','audit / pre-push','effectful Rust verifier','broker','filter'),
    ('remote','Public remote','server hook deployment','assumed','cloud'),
))
nodes=mark(nodes,
    git=('trusted-platform','A7','Commit tree / OID semantics'),
    shape=('source-proof','record_envelope_ok_spec','Shape only, NOT tag authentication'),
    audit=('tested','A4','Actual Rust Git traversal and checks'),
    remote=('trusted-platform','A13','Remote hook deployment depends on operator'),
)
links=(route(nodes,'git','shape','inspect','public committed blob','provider'),
       route(nodes,'shape','audit','verdict','envelope shape result','proved'),
       route(nodes,'audit','remote','push','commit plus audit outcome','broker'))
PLAN=Diagram(
    key='audit',title='Audit: a shape check is not authentication',
    kicker='Keyless checks can catch plaintext and malformed records; authenticity requires the secret key.',
    nodes=nodes,links=links,beats=(
        Beat('tree','The audit reads commit trees and staged history with raw paths and object IDs supplied by Git.',
             nodes=tuple(n.key for n in nodes),status='assumed',
             knowledge=info4(nodes,(('staged commits and blobs','public paths'),
                                  ('22-byte header expected','config identifier'),
                                  ('no secret key needed','audit may be keyed'),
                                  ('no automatic deployment',)))),
        Beat('check','The source-derived envelope check verifies record shape only; a forger can mimic the format.',
             links=('inspect',),packet='inspect',packet_label='Git blob bytes',packet_kind='ciphertext',
             processing=Processing('shape','public blob','shape valid?','ciphertext','decision'),status='proved'),
        Beat('audit','The tested auditor rejects invalid envelopes and can authenticate records when an unlocked key is available.',
             links=('verdict',),packet='verdict',packet_label='shape verdict',packet_kind='decision',
             processing=Processing('audit','path + envelope','allow / refuse','metadata','decision'),status='tested'),
        Beat('remote','A local pre-push hook or installed server-side audit is a deployment decision, not a Lean proof.',
             links=('push',),packet='push',packet_label='commit objects',packet_kind='ciphertext',
             processing=Processing('remote','incoming commits','enforced?','ciphertext','decision'),status='assumed',
             knowledge=info4(nodes,(('content addressing','assumed Git behavior'),
                                  ('record_envelope_ok','source-derived proof'),
                                  ('A14: format != tag','keyed if unlocked'),
                                  ('A13: server policy','must be installed')))),
    ),footer='No keyless authentication; remote prevention depends on deployed enforcement (A13/A14).')
PLAN=carry_knowledge(PLAN)
