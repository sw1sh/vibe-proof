# Side check of the evidence "at smaller b the reachable set leaks": for every state x of the exported
# trap (width B), project x to width b < B and test whether the width-b relaxation reachable set from it
# admits the export-style consistent labelling (outputs g(phase) at white phases, i.e. u with pos by phase).
import sys
from collections import deque
D = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/newideas/'
def r30(l, c, r): return (30 >> (4*l + 2*c + r)) & 1
def succ(w, b, ph, s):
    row = [int(w[ph])] + [(s >> (p-1)) & 1 for p in range(1, b+1)]
    out = set()
    for r in (0, 1):
        ext = row + [r]
        s2 = 0
        for p in range(1, b+1): s2 |= r30(ext[p-1], ext[p], ext[p+1]) << (p-1)
        out.add(((ph+1) % len(w), s2))
    return out
def reach_ok(w, b, x0, g, cap=200000):
    seen = {x0}; dq = deque([x0])
    while dq:
        ph, s = dq.popleft()
        if w[ph] == '0' and (s & 1) != g[ph]: return False, len(seen)
        for y in succ(w, b, ph, s):
            if y not in seen:
                seen.add(y); dq.append(y)
                if len(seen) > cap: return None, len(seen)
    return True, len(seen)
fn, b, g = sys.argv[1], int(sys.argv[2]), [int(c) for c in sys.argv[3]]
L = [l.split() for l in open(D + fn).read().strip().split('\n')]
w, B, n = L[0]; B = int(B)
starts = sorted({(int(ph), int(s) & ((1 << b) - 1)) for ph, s, _ in L[1:]})
res = {}
for x0 in starts:
    ok, sz = reach_ok(w, b, x0, g)
    res[ok] = res.get(ok, 0) + 1
print(f"{fn} projected to b={b}: {len(starts)} distinct projected starts; consistent-reach counts {res}")
