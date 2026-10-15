# From-scratch existence check (Tarjan SCC + counter labelling), independent of cert.py and of the Lean tables.
# A certificate exists iff every SCC that contains a cycle admits pos: SCC -> Z_m with
# pos(y) = pos(x) + [x white] on internal edges and a word u with col1(x) = u[pos(x)] at white x.
# (Ranks = reverse topological index of SCCs.)  We compute the finest such m via cycle-sum gcd.
import sys
from math import gcd
sys.setrecursionlimit(100000)
def graph(w, b):
    P = len(w); N = P << b
    adj = [[] for _ in range(N)]
    for phi in range(P):
        c0 = int(w[phi])
        for s in range(1 << b):
            for x in (0, 1):
                cols = [c0] + [(s >> (i - 1)) & 1 for i in range(1, b + 1)] + [x]
                ns = sum((cols[i - 1] ^ (cols[i] | cols[i + 1])) << (i - 1) for i in range(1, b + 1))
                v = ((phi + 1) % P << b) | ns
                if v not in adj[(phi << b) | s]: adj[(phi << b) | s].append(v)
    return P, N, adj
def tarjan(N, adj):
    index = [None] * N; low = [0] * N; on = [False] * N; st = []; comp = [None] * N; cnt = [0]; nc = [0]
    def sc(v):
        index[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on[v] = True
        for y in adj[v]:
            if index[y] is None: sc(y); low[v] = min(low[v], low[y])
            elif on[y]: low[v] = min(low[v], index[y])
        if low[v] == index[v]:
            while True:
                y = st.pop(); on[y] = False; comp[y] = nc[0]
                if y == v: break
            nc[0] += 1
    for v in range(N):
        if index[v] is None: sc(v)
    return comp, nc[0]
def analyse(w, b):
    P, N, adj = graph(w, b); comp, nc = tarjan(N, adj)
    white = lambda v: w[v >> b] == "0"
    col1 = lambda v: v & 1
    members = {}
    for v in range(N): members.setdefault(comp[v], []).append(v)
    ok = True; words = set()
    for c, vs in members.items():
        cyc = len(vs) > 1 or any(y == vs[0] for y in adj[vs[0]])
        if not cyc: continue
        # potential: lab(v) = number of white steps from root along a BFS tree; g = gcd of cycle defects
        root = vs[0]; lab = {root: 0}; q = [root]; g = 0
        while q:
            nq = []
            for x in q:
                for y in adj[x]:
                    if comp[y] != c: continue
                    nl = lab[x] + (1 if white(x) else 0)
                    if y in lab: g = gcd(g, abs(nl - lab[y]))
                    else: lab[y] = nl; nq.append(y)
            q = nq
        if g == 0:  # no white step on any cycle would mean an all-black cycle: impossible unless w all black
            ok = False; continue
        # outputs must be a function of lab mod m for some m | g; take the smallest m | g that works
        found = None
        for m in sorted(d for d in range(1, g + 1) if g % d == 0):
            u = {}
            good = True
            for v in vs:
                if white(v):
                    k = lab[v] % m
                    if u.setdefault(k, col1(v)) != col1(v): good = False; break
            if good: found = (m, "".join(str(u.get(k, 0)) for k in range(m))); break
        if found is None: ok = False
        else: words.add(found)
    return ok, nc, sorted(words)
for arg in sys.argv[1:]:
    w, b = arg.split(":"); b = int(b)
    ok, nc, words = analyse(w, b)
    print(w, "b=%d" % b, "SCCs=%d" % nc, "certificate exists" if ok else "NO certificate", words)
