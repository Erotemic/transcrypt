"""Attribute-based selection implemented in the current source; Git remains trusted."""
from tvis.diagram import Processing, Beat, Diagram
from tvis.plans.common import carry_knowledge, mark, info4, route, row4

nodes = row4((
    ('developer', 'Developer', 'chooses protected paths', 'guest', 'laptop'),
    ('attrs', '.gitattributes', 'Git selection policy', 'policy', 'config'),
    ('git', 'Git attributes', 'matching + precedence', 'assumed', 'git'),
    ('core', 'v3 core', 'path-bound auth', 'proved', 'shield'),
))
nodes=mark(nodes,
    git=('trusted-platform', 'A19', 'Git evaluates attributes; tested, not proved'),
    core=('source-proof', 'parse_attr_response_spec', 'Parses exact-path answers; canonical policy is also proved'),
)
links = (route(nodes, 'developer', 'attrs', 'declare', 'declares patterns', 'policy'),
         route(nodes, 'attrs', 'git', 'match', 'Git check-attr', 'assumed'),
         route(nodes, 'git', 'core', 'bind', 'raw Git path', 'broker'))
PLAN = Diagram(
    key='selection', title='What gets encrypted?',
    kicker='Selection is policy. Authentication must use the exact selected Git pathname.',
    nodes=nodes, links=links, beats=(
        Beat('today', 'Selected paths now use native Git attributes: *.secret, .env and private/** can all be protected.',
             nodes=tuple(n.key for n in nodes), status='implemented',
             knowledge=info4(nodes, (('names desired secrets', 'explicitly opts in'),
                                  ('filter attributes', 'arbitrary Git patterns'),
                                  ('evaluates attributes', 'raw path bytes'),
                                  ('canonical protected path', 'exact path binding')))),
        Beat('choose', 'Implemented: use .env, private/**, or other Git attribute patterns—not a second glob language.',
             links=('declare',), packet='declare', packet_label='.env + private/**', status='implemented', packet_kind='path',
             processing=Processing('git', 'Git patterns', 'selected path', 'path', 'path')),
        Beat('match', 'Git decides which paths have the filter; its attribute semantics remain external assumptions.',
             links=('match',), packet='match', packet_label='selection', status='assumed', packet_kind='path',
             processing=Processing('git', 'path + attrs', 'yes / no', 'path', 'decision')),
        Beat('bind', 'The source-derived parser checks the exact attribute answer; the protocol binds the raw Git path.',
             links=('bind',), packet='bind', packet_label='raw path', status='proved', packet_kind='path',
             processing=Processing('core', 'attribute reply', 'exact verdict', 'metadata', 'decision')),
    ), footer="Pattern selection is implemented; Git’s attribute evaluation remains trusted (A19).")

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
