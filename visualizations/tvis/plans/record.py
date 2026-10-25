"""Exploded-view reading of the authenticated file envelope, not literal nesting."""
from tvis.diagram import Beat, Diagram, Layer, Link, Node, Package

layers=Layer('envelope', 'V3 file record', 'public bytes in a Git object', 'plain',
             Layer('header', '22-byte header', '6-byte marker + 16-byte config id', 'plain',
                   Layer('tag', '16-byte AES-SIV tag', 'authentication check (trusted primitive)', 'sealed',
                         Layer('ciphertext', 'Encrypted content', 'only authenticated opening releases plaintext', 'encrypted'))))
nodes=(Node('author','Local user','knows plaintext',(-5.45,1.62),2.20,1.08,'guest',icon='laptop'),
       Node('reader','Public observer','only record bytes',(5.45,1.62),2.20,1.08,'provider',icon='cloud'))
links=(Link('publish','author','reader','Git object',((-4.35,1.62),(-3.65,2.38),(3.65,2.38),(4.35,1.62)),
            'provider',label_xy=(0,2.54)),)
PLAN=Diagram(
    key='record', title='What the public Git blob contains',
    kicker='X-ray illustration: field labels reveal structure, not the secret to a public reader.',
    nodes=nodes,links=links,packages=(Package('v3record',(0,-0.19),6.00,4.68,layers),),
    beats=(
        Beat('whole', 'An authenticated v3 record replaces the selected plaintext in Git history.',
             nodes=('author','reader'), packages=('v3record',), layer_focus='envelope',status='implemented'),
        Beat('header', 'The first 22 bytes contain a six-byte file marker and the authenticated config identifier.',
             layer_focus='header',status='proved'),
        Beat('tag', 'The next 16 bytes carry the SIV tag; correctness of RustCrypto is an external contract.',
             layer_focus='tag',status='assumed'),
        Beat('content', 'The remaining bytes are encrypted content; config and exact Git path are authenticated data.',
             layer_focus='ciphertext',status='proved'),
        Beat('public', 'The public observer receives the entire record, not the decryption key.',
             links=('publish',),packet='publish',packet_label='record bytes',status='implemented'),
    ), footer='Fields are concatenated on disk; the nested rectangles are successive explanatory zooms, not nested encryption.')
