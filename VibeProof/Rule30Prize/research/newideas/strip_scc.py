# Local (finite-strip) relaxation of "c is eventually w^inf".
# Strip = columns 1..b of the right half, column 0 = c = w^inf (phase phi = t mod P).
# Transition at phase phi: s'_p = s_{p-1} xor (s_p or s_{p+1}) for p = 1..b-1 (s_0 = c(phi)),
#   s'_b = not s_{b-1} if s_b = 1, else free (column b+1 is outside the strip).
# Output: col_1 = s_1 at phases with w[phi] = 0 (zeros of c).
# Claim checked: every infinite path has eventually periodic output  <=  every nontrivial SCC admits a
# consistent "position" labelling (all cycles' outputs are powers of one primitive word).
import sys
sys.setrecursionlimit(10000)
def succs(w, b, phi, s):
    # s: int, bit p-1 <-> column p (p = 1..b)
    cphi = int(w[phi])
    bit = lambda x, p: (x >> (p - 1)) & 1 if 1 <= p <= b else (cphi if p == 0 else None)
    base = 0
    for p in range(1, b):
        v = bit(s, p - 1) ^ (bit(s, p) | bit(s, p + 1))
        base |= v << (p - 1)
    if bit(s, b) == 1:
        return [base | ((1 ^ bit(s, b - 1)) << (b - 1))]
    return [base, base | (1 << (b - 1))]
def analyze(w, b):
    P = len(w)
    N = P << b
    node = lambda phi, s: (phi << b) | s
    adj = [None] * N
    for phi in range(P):
        for s in range(1 << b):
            adj[node(phi, s)] = [node((phi + 1) % P, s2) for s2 in succs(w, b, phi, s)]
    # Tarjan iterative
    index = [0] * N; low = [0] * N; onst = [False] * N; idx = [-1] * N
    stack = []; comp = [-1] * N; ncomp = 0; counter = 0
    for root in range(N):
        if idx[root] != -1: continue
        work = [(root, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                idx[v] = low[v] = counter; counter += 1; stack.append(v); onst[v] = True
            recurse = False
            nb = adj[v]
            while i < len(nb):
                u = nb[i]; i += 1
                if idx[u] == -1:
                    work.append((v, i)); work.append((u, 0)); recurse = True; break
                elif onst[u]:
                    low[v] = min(low[v], idx[u])
            if recurse: continue
            if low[v] == idx[v]:
                while True:
                    u = stack.pop(); onst[u] = False; comp[u] = ncomp
                    if u == v: break
                ncomp += 1
            if work:
                pv, _ = work[-1]
                low[pv] = min(low[pv], low[v])
    # group
    members = {}
    for v in range(N): members.setdefault(comp[v], []).append(v)
    out = lambda v: ((v & 1) if w[v >> b] == '0' else None)   # s_1 = bit 0
    results = []
    for cid, vs in members.items():
        vset = set(vs)
        # nontrivial?
        if len(vs) == 1 and vs[0] not in adj[vs[0]]: continue
        # find a cycle from vs[0] inside SCC via BFS back to itself
        start = vs[0]
        prev = {start: None}; q = [start]; found = None
        while q and found is None:
            nq = []
            for x in q:
                for y in adj[x]:
                    if y not in vset: continue
                    if y == start: found = x; break
                    if y not in prev: prev[y] = x; nq.append(y)
                if found is not None: break
            q = nq
        path = [found]
        while prev[path[-1]] is not None: path.append(prev[path[-1]])
        path = path[::-1]   # start ... found, then edge back to start
        word = [out(v) for v in path if out(v) is not None]
        # primitive root of word
        L = len(word)
        u = None
        for d in range(1, L + 1):
            if L % d == 0 and word == word[:d] * (L // d): u = word[:d]; break
        m = len(u)
        pos = {start: 0}; q = [start]; ok = True
        while q and ok:
            nq = []
            for x in q:
                o = out(x)
                if o is not None:
                    if o != u[pos[x] % m]: ok = False; break
                    np_ = (pos[x] + 1) % m
                else:
                    np_ = pos[x]
                for y in adj[x]:
                    if y not in vset: continue
                    if y in pos:
                        if pos[y] != np_: ok = False; break
                    else:
                        pos[y] = np_; nq.append(y)
                if not ok: break
            q = nq
        results.append((len(vs), ok, ''.join(map(str, u))))
    return results
if __name__ == '__main__':
    w = sys.argv[1]
    for b in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
        res = analyze(w, b)
        bad = [r for r in res if not r[1]]
        print(f"w={w} b={b}: nontrivial SCCs={len(res)}, non-periodic-output SCCs={len(bad)}",
              (sorted(res, key=lambda r: -r[0])[:6]), flush=True)
