# Independent certificate generator + checker for the strip relaxation of "column 0 = w^inf".
# Node (phi, s): phi = phase in Z_P, s in {0,1}^b (bit p-1 = column p).
# Edge (phi, s) -> (phi+1, s') iff s' is consistent with rule 30 at columns 1..b
#   (columns 1..b-1 exact, column b: forced to !s_{b-1} if s_b = 1, free otherwise).
# Output at (phi, s) when w[phi] == '0': s_1 (column 1).
# Certificate: rank(node) in N and pos(node) in Z_m(rank) with word u(rank) such that for every edge x->y:
#   rank(y) <= rank(x); and if rank(y) == rank(x) then
#     pos(y) == pos(x) + [x has output] (mod m) and (x has output -> out(x) == u[pos(x)]).
# Soundness: along any infinite path rank is eventually constant, after which outputs follow u periodically.
import sys
sys.setrecursionlimit(1 << 20)
def build(w, b):
    P = len(w)
    nodes = [(phi, s) for phi in range(P) for s in range(1 << b)]
    def bit(s, p, cphi):
        return cphi if p == 0 else (s >> (p - 1)) & 1
    adj = {}
    for phi, s in nodes:
        cphi = int(w[phi])
        base = 0
        for p in range(1, b):
            base |= (bit(s, p - 1, cphi) ^ (bit(s, p, cphi) | bit(s, p + 1, cphi))) << (p - 1)
        if bit(s, b, cphi):
            succ = [base | ((1 ^ bit(s, b - 1, cphi)) << (b - 1))]
        else:
            succ = [base, base | (1 << (b - 1))]
        adj[(phi, s)] = [((phi + 1) % P, x) for x in succ]
    return nodes, adj
def kosaraju(nodes, adj):
    order = []; seen = set()
    for v in nodes:
        if v in seen: continue
        stack = [(v, iter(adj[v]))]; seen.add(v)
        while stack:
            x, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                order.append(x); stack.pop()
            elif nxt not in seen:
                seen.add(nxt); stack.append((nxt, iter(adj[nxt])))
    radj = {v: [] for v in nodes}
    for v in nodes:
        for y in adj[v]: radj[y].append(v)
    comp = {}; c = 0
    for v in reversed(order):
        if v in comp: continue
        stack = [v]; comp[v] = c
        while stack:
            x = stack.pop()
            for y in radj[x]:
                if y not in comp: comp[y] = c; stack.append(y)
        c += 1
    return comp, c   # components numbered in topological order of the condensation (sources first)
def certify(w, b):
    nodes, adj = build(w, b)
    comp, nc = kosaraju(nodes, adj)
    out = lambda v: (v[1] & 1) if w[v[0]] == '0' else None
    rank = {v: nc - 1 - comp[v] for v in nodes}   # sources get high rank, edges go to >= comp index -> rank non-increasing
    members = {}
    for v in nodes: members.setdefault(comp[v], []).append(v)
    pos = {}; words = {}
    for c, vs in members.items():
        vset = set(vs)
        nontriv = len(vs) > 1 or any(y == vs[0] for y in adj[vs[0]])
        if not nontriv:
            for v in vs: pos[v] = 0
            words[c] = [0]
            continue
        st = vs[0]
        # cycle through st
        prev = {st: None}; q = [st]; back = None
        while q and back is None:
            nq = []
            for x in q:
                for y in adj[x]:
                    if comp.get(y) != c: continue
                    if y == st: back = x; break
                    if y not in prev: prev[y] = x; nq.append(y)
                if back is not None: break
            q = nq
        path = [back]
        while prev[path[-1]] is not None: path.append(prev[path[-1]])
        path.reverse()
        word = [out(v) for v in path if out(v) is not None]
        L = len(word)
        m = next(d for d in range(1, L + 1) if L % d == 0 and word == word[:d] * (L // d))
        u = word[:m]
        pos[st] = 0; q = [st]; ok = True
        while q and ok:
            nq = []
            for x in q:
                o = out(x)
                if o is not None:
                    if o != u[pos[x] % m]: ok = False; break
                    np_ = (pos[x] + 1) % m
                else: np_ = pos[x]
                for y in adj[x]:
                    if comp[y] != c: continue
                    if y in pos:
                        if pos[y] != np_: ok = False; break
                    else: pos[y] = np_; nq.append(y)
                if not ok: break
            q = nq
        if not ok: return None
        words[c] = u
    return nodes, adj, rank, pos, {nc - 1 - c: u for c, u in words.items()}
def check(w, b, cert):
    nodes, adj, rank, pos, words = cert
    out = lambda v: (v[1] & 1) if w[v[0]] == '0' else None
    for x in nodes:
        for y in adj[x]:
            if rank[y] > rank[x]: return f"rank increases on {x}->{y}"
            if rank[y] == rank[x]:
                u = words[rank[x]]; m = len(u); o = out(x)
                if o is not None:
                    if o != u[pos[x] % m]: return f"output mismatch at {x}"
                    if pos[y] != (pos[x] + 1) % m: return f"pos mismatch {x}->{y}"
                else:
                    if pos[y] != pos[x]: return f"pos mismatch {x}->{y}"
    return "OK"
if __name__ == '__main__':
    for arg in sys.argv[1:]:
        w, b = arg.split(':'); b = int(b)
        cert = certify(w, b)
        if cert is None: print(w, b, "no certificate (some SCC has inconsistent outputs)"); continue
        print(w, b, "certificate check:", check(w, b, cert), "| ranks:", len(set(cert[2].values())),
              "| words:", sorted(set(''.join(map(str, u)) for u in cert[4].values())))
