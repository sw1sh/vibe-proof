# Independent semantic check of the strip relaxation (no use of cert.py or the Lean tables):
# Graph: nodes (phi, s), s in {0,1}^b (bit i = column i+1); edges (phi,s)->(phi+1 mod P, lin3(w_phi::s++[x])).
# Every infinite path ends in one nontrivial SCC. In an SCC S, define edge weight [w_phi = 0] (white phase);
# g = gcd of cycle weights = gcd over edges of (pot(x) + wt - pot(y)) for a BFS potential.
# Claim holds iff for every nontrivial SCC: column 1 at white nodes is a function of pot mod g
# (then outputs along any path in S are periodic in the white-count with period g).
# Also: if g == 0 (no white phase in any cycle) the condition is vacuous.
import sys
from math import gcd

def build(w, b):
    P = len(w)
    N = P << b
    adj = [None] * N
    for phi in range(P):
        c = w[phi]
        for s in range(1 << b):
            bits = [c] + [(s >> i) & 1 for i in range(b)]
            succ = []
            for x in (0, 1):
                l = bits + [x]
                ns = 0
                for i in range(b):
                    ns |= (l[i] ^ (l[i + 1] | l[i + 2])) << i
                succ.append(((phi + 1) % P) * (1 << b) + ns)
            adj[phi * (1 << b) + s] = sorted(set(succ))
    return adj

def tarjan(adj):
    N = len(adj)
    index = [-1] * N; low = [0] * N; onst = [False] * N; st = []; comp = [-1] * N
    idx = 0; nc = 0
    for v0 in range(N):
        if index[v0] != -1: continue
        work = [(v0, 0)]
        index[v0] = low[v0] = idx; idx += 1; st.append(v0); onst[v0] = True
        while work:
            v, i = work[-1]
            if i < len(adj[v]):
                work[-1] = (v, i + 1)
                y = adj[v][i]
                if index[y] == -1:
                    index[y] = low[y] = idx; idx += 1; st.append(y); onst[y] = True
                    work.append((y, 0))
                elif onst[y]:
                    low[v] = min(low[v], index[y])
            else:
                work.pop()
                if work:
                    p = work[-1][0]; low[p] = min(low[p], low[v])
                if low[v] == index[v]:
                    while True:
                        y = st.pop(); onst[y] = False; comp[y] = nc
                        if y == v: break
                    nc += 1
    return comp, nc

def analyze(wstr, b, verbose=False):
    w = [int(ch) for ch in wstr]
    P = len(w)
    adj = build(w, b)
    comp, nc = tarjan(adj)
    members = {}
    for v, c in enumerate(comp): members.setdefault(c, []).append(v)
    ok = True; summary = []
    for c, vs in members.items():
        nontriv = len(vs) > 1 or vs[0] in adj[vs[0]]
        if not nontriv: continue
        S = set(vs)
        pot = {vs[0]: 0}; q = [vs[0]]
        while q:
            x = q.pop()
            wt = 1 if w[x >> b] == 0 else 0
            for y in adj[x]:
                if y in S and y not in pot:
                    pot[y] = pot[x] + wt; q.append(y)
        g = 0
        for x in vs:
            wt = 1 if w[x >> b] == 0 else 0
            for y in adj[x]:
                if y in S: g = gcd(g, abs(pot[x] + wt - pot[y]))
        # outputs at white nodes as a function of pot mod g
        f = {}
        consistent = True
        for x in vs:
            if w[x >> b] == 0:
                key = pot[x] % g if g else pot[x]
                o = (x & ((1 << b) - 1)) & 1
                if key in f and f[key] != o: consistent = False
                f.setdefault(key, o)
        if g == 0:
            # no cycle passes a white phase: impossible when w has a zero (every cycle has length multiple of P)
            pass
        u = ''.join(str(f.get(k, '?')) for k in range(g)) if g else '-'
        summary.append((len(vs), g, consistent, u))
        if not consistent: ok = False
    return ok, summary, nc

if __name__ == '__main__':
    for arg in sys.argv[1:]:
        wstr, b = arg.split(':'); b = int(b)
        ok, summ, nc = analyze(wstr, b)
        bad = [s for s in summ if not s[2]]
        words = sorted(set((s[1], s[3]) for s in summ if s[2]))
        print(wstr, 'b=%d' % b, 'SCCs=%d' % nc, 'nontrivial=%d' % len(summ), 'claim_holds=%s' % ok,
              'bad_SCCs=%d' % len(bad), 'eventual (g,u) words:', words[:12])
