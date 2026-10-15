# Verifier: is the bad-class language (Lean `occurs` semantics) at width b exactly the gap shift
# {no 11, no 00000}?  Product of the subset automaton with the gap-shift automaton, all lengths.
import sys
sys.path.insert(0, '.')
from badclass import bad_class
def analyze(b):
    nodes, E, comps, B = bad_class(b)
    def start(y): return frozenset(v for v in B if v[0] == 0 and v[1][0] == y)
    def step(S, y):
        out = set()
        for v in S:
            for v1 in E[v]:
                if v1 in B:
                    for v2 in E[v1]:
                        if v2 in B and v2[1][0] == y: out.add(v2)
        return frozenset(out)
    def gnext(g, y):  # g = (last1, zrun); None = no letter yet
        if g is None: return (y == 1, 0 if y == 1 else 1)
        last1, z = g
        if y == 1: return None if last1 else (True, 0)
        return None if z >= 4 else (False, z + 1)
    seen = set(); frontier = []
    for y in (0, 1):
        S = start(y); g = gnext(None, y)
        if not S: return ('forbidden', [y])
        frontier.append((S, g, [y]))
    forbidden = []
    while frontier:
        S, g, w = frontier.pop()
        if (S, g) in seen: continue
        seen.add((S, g))
        for y in (0, 1):
            g2 = gnext(g, y)
            if g2 is None: continue
            S2 = step(S, y)
            if not S2:
                forbidden.append(w + [y]); continue
            frontier.append((S2, g2, w + [y]))
    return ('states', len(seen), 'example forbidden words beyond gap shift (shortest first)',
            sorted({''.join(map(str, f)) for f in forbidden}, key=len)[:6])
for b in (3, 4, 5):
    print('b =', b, analyze(b))
