# Jen-augmented strip relaxation: for each bad SCC, check whether some strip column p (all phases) or some
# masked combination is forced periodic inside the SCC (consistent position labelling).  If so, any path
# staying in that SCC has an eventually periodic column p >= 1, contradicting Jen (columns 0 and p).
import sys
sys.path.insert(0, '.')
exec(open('cert.py').read().split("if __name__ == '__main__':")[0])
def labeling_ok(vs, adj, comp, c, outf):
    st = vs[0]
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
    word = [outf(v) for v in path if outf(v) is not None]
    L = len(word)
    if L == 0: return True
    m = next(d for d in range(1, L + 1) if L % d == 0 and word == word[:d] * (L // d))
    u = word[:m]
    pos = {st: 0}; q = [st]
    while q:
        nq = []
        for x in q:
            o = outf(x)
            if o is not None:
                if o != u[pos[x] % m]: return False
                np_ = (pos[x] + 1) % m
            else: np_ = pos[x]
            for y in adj[x]:
                if comp[y] != c: continue
                if y in pos:
                    if pos[y] != np_: return False
                else: pos[y] = np_; nq.append(y)
        q = nq
    return True
w = sys.argv[1]; b = int(sys.argv[2])
nodes, adj = build(w, b)
comp, nc = kosaraju(nodes, adj)
members = {}
for v in nodes: members.setdefault(comp[v], []).append(v)
for c, vs in members.items():
    if not (len(vs) > 1 or any(y == vs[0] for y in adj[vs[0]])): continue
    out1 = lambda v: (v[1] & 1) if w[v[0]] == '0' else None
    if labeling_ok(vs, adj, comp, c, out1): continue
    rigid = [p for p in range(1, b + 1) if labeling_ok(vs, adj, comp, c, lambda v, p=p: (v[1] >> (p - 1)) & 1)]
    print(f"bad SCC size {len(vs)}: columns forced periodic inside: {rigid}")
# masked pairs (col_p, col_{p+1} on zeros of col_p), p = 1..b-1
for c, vs in members.items():
    if not (len(vs) > 1 or any(y == vs[0] for y in adj[vs[0]])): continue
    out1 = lambda v: (v[1] & 1) if w[v[0]] == '0' else None
    if labeling_ok(vs, adj, comp, c, out1): continue
    rigidm = [p for p in range(1, b) if labeling_ok(vs, adj, comp, c,
              lambda v, p=p: (((v[1] >> (p - 1)) & 1), (0 if ((v[1] >> (p - 1)) & 1) else ((v[1] >> p) & 1) + 2)))]
    print(f"bad SCC size {len(vs)}: masked pairs forced periodic inside: {rigidm}")
