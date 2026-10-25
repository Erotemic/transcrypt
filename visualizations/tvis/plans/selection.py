"""Current suffix policy versus the user-selected Git-attribute design goal."""
from tvis.diagram import Beat, Diagram
from tvis.plans.common import carry_knowledge, info4, route, row4

nodes = row4((
    ('developer', 'Developer', 'chooses protected paths', 'guest', 'laptop'),
    ('attrs', '.gitattributes', 'Git selection policy', 'policy', 'config'),
    ('git', 'Git attributes', 'matching + precedence', 'assumed', 'git'),
    ('core', 'v3 core', 'path-bound auth', 'proved', 'shield'),
))
links = (route(nodes, 'developer', 'attrs', 'declare', 'declares patterns', 'policy'),
         route(nodes, 'attrs', 'git', 'match', 'Git check-attr', 'assumed'),
         route(nodes, 'git', 'core', 'bind', 'raw Git path', 'broker'))
PLAN = Diagram(
    key='selection', title='What gets encrypted?',
    kicker='Selection is policy. Authentication must use the exact selected Git pathname.',
    nodes=nodes, links=links, beats=(
        Beat('today', 'In the audited v3 snapshot, protected files are constrained to *.secret.',
             nodes=tuple(n.key for n in nodes), status='implemented',
             knowledge=info4(nodes, (('names desired secrets', 'explicitly opts in'),
                                  ('filter attributes', 'currently *.secret'),
                                  ('evaluates attributes', 'raw path bytes'),
                                  ('canonical protected path', 'exact path binding')))),
        Beat('choose', 'Design goal: .env, private/**, or any Git attribute pattern—not a second glob language.',
             links=('declare',), packet='declare', packet_label='.env + private/**', status='planned'),
        Beat('match', 'Git decides which paths have the filter; its attribute semantics remain external assumptions.',
             links=('match',), packet='match', packet_label='selection', status='assumed'),
        Beat('bind', 'The core authenticates the literal path it receives, not a filename extension.',
             links=('bind',), packet='bind', packet_label='raw path', status='planned'),
    ), footer='Arbitrary patterns are the product target; this scene does not claim they were shipped in snapshot 861975a.')

# Every rendered beat carries a complete snapshot of current information.
PLAN = carry_knowledge(PLAN)
