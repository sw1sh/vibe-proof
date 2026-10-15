# Verifier: brute-force minimal closed sets (via forward reachability) of the driven strip graph, to
# cross-validate sccbad.c at small widths.
import sys
from math import gcd
w = [int(c) for c in sys.argv[1]]; b = int(sys.argv[2]); P = len(w); M = 1 << b; mask = M - 1
def succ(v):
    f, r = divmod(v, M); g = (f + 1) % P
    return [g * M + ((((r << 1) | w[f]) ^ (r | (r >> 1) | (z << (b - 1)))) & mask) for z in (0, 1)]
N = P * M
def reach(v):
    seen = {v}; st = [v]
    while st:
        u = st.pop()
        for x in succ(u):
            if x not in seen: seen.add(x); st.append(x)
    return seen
R = [None] * N
minimal = set()
for v in range(N):
    S = frozenset(reach(v))
    # S is a minimal closed set iff every node of S reaches v (then reach(u) = S for all u in S)
    if all(v in reach(u) for u in list(S)[:50]) and all(v in reach(u) for u in S):
        minimal.add(S)
    if len(minimal) and v > 3 * M // 2 and len(minimal) == 1:
        pass
print("w=%s b=%d: minimal closed sets: %d, sizes %s" % (sys.argv[1], b, len(minimal), sorted(len(S) for S in minimal)))
for S in minimal:
    root = min(S); lev = {root: 0}; q = [root]; d = 0
    for u in q:
        for x in succ(u):
            if x not in lev: lev[x] = lev[u] + 1; q.append(x)
            else: d = gcd(d, lev[u] + 1 - lev[x])
    cls = {}; bad = False
    for v in S:
        f, r = divmod(v, M)
        if w[f]: continue
        k = lev[v] % d; o = r & 1
        if cls.setdefault(k, o) != o: bad = True
    vals = {f: sorted({(v % M) & 1 for v in S if v // M == f}) for f in range(P)}
    print("  size %d period %d %s col1 by phase %s" % (len(S), d, "BAD" if bad else "GOOD", vals))
