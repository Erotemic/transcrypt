"""Flush checked worktrees and forget the unlock key only on full success."""
from tvis.diagram import Beat, Diagram, Processing
from tvis.plans.common import carry_knowledge, info4, mark, route, row4

nodes=row4((
    ('disk','Unlocked checkout','ordinary local plaintext','secret','laptop'),
    ('snapshot','Index + worktree','verify and reseal','broker','git'),
    ('gate','lock_action gate','actual Rust decision','proved','shield'),
    ('writer','OS writer + key erase','replace, then forget','assumed','database'),
))
nodes=mark(nodes,
    snapshot=('tested','A4','Index/unstaged edit checks; Git semantics A7'),
    gate=('source-proof','lock_action_spec','Source-derived pure action; model lockEntry_spec separate'),
    writer=('tested','A8','Stamped filesystem effects; agent/key deletion not proved'),
)
links=(route(nodes,'disk','snapshot','read','plaintext + index state','secret'),
       route(nodes,'snapshot','gate','decide','current + sealed bytes','broker'),
       route(nodes,'gate','writer','flush','only authorized rewrite','proved'))
PLAN=Diagram(
    key='lock',title='Lock: refuse unsafe loss, flush, then forget the key',
    kicker='The actual lock action is source-derived proved; replacement and erasure are native operations.',
    nodes=nodes,links=links,beats=(
        Beat('local','A checked-out file is still plaintext; the key has not been forgotten.',
             nodes=tuple(n.key for n in nodes),status='implemented',
             knowledge=info4(nodes,(('locally editable bytes','current key still usable'),
                                  ('index path + blob OID','worktree stamp'),
                                  ('needs recoverable record',),('no writes yet',)))),
        Beat('snapshot','The adapter checks the staged index, local edits and record recoverability before flush.',
             links=('read',),packet='read',packet_label='plaintext + state',packet_kind='plaintext',
             processing=Processing('snapshot','staged + worktree','recoverability','metadata','decision'),status='tested'),
        Beat('gate','The source-derived lock_action permits a recoverable flush or refuses data-losing replacements.',
             links=('decide',),packet='decide',packet_label='record + reseal',packet_kind='ciphertext',
             processing=Processing('gate','worktree / record','Flush / Keep / Err','metadata','decision'),status='proved'),
        Beat('flush','The tested native writer replaces files after stamp checks. A refusal keeps the key available.',
             links=('flush',),packet='flush',packet_label='authorized ciphertext',packet_kind='ciphertext',
             processing=Processing('writer','approved record','locked worktree','decision','ciphertext'),status='tested',
             knowledge=info4(nodes,(('ciphertext after success',),('verified staged record','no stray edits'),
                                  ('lock_action_spec','lockEntry MODEL'),
                                  ('writes/renames A8','key forgotten last')))),
        Beat('forget','Only after all worktrees flush does the command forget the stored key or stop the private agent.',
             focus=('writer',),status='tested',
             processing=Processing('writer','all worktrees OK','forget key','decision','key')),
    ),footer='lock never promises secure erasure of existing plaintext copies; crash/race semantics remain A8.')
PLAN=carry_knowledge(PLAN)
