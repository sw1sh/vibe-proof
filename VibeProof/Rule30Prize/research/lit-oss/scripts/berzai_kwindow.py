# Independent implementation of the K-window subset automaton + single-cycle criterion
# (as stated in Berzai, Part I, Sections "K-window automaton" and "period graph").
import sys
def make(K):
    mask = (1 << K) - 1
    def phi_all(w, c):
        base = (((w << 1) | c) ^ (w | (w >> 1))) & mask      # cell K+1 = 0
        wkm1 = (w >> (K - 2)) & 1
        alt = (base & ~(1 << (K - 1))) | ((wkm1 ^ 1) << (K - 1))  # cell K+1 = 1
        return (base, alt)
    def step(S, c):
        out = set()
        for w in S:
            out.update(phi_all(w, c))
        return frozenset(out)
    return mask, step
def certify(word, K, max_states=20000):
    mask, step = make(K)
    ALL = frozenset(range(1 << K))
    def edges(S):
        # DFS through the word; branch on interface bit at zero positions
        res = []  # list of (label tuple, target)
        stack = [(0, S, ())]
        while stack:
            pos, cur, lab = stack.pop()
            if pos == len(word):
                if cur: res.append((lab, cur))
                continue
            if word[pos] == 1:
                nxt = step(cur, 1)
                if nxt: stack.append((pos + 1, nxt, lab))
            else:
                for u in (0, 1):
                    sub = frozenset(w for w in cur if (w & 1) == u)
                    if sub:
                        nxt = step(sub, 0)
                        if nxt: stack.append((pos + 1, nxt, lab + (u,)))
        return res
    verts = {ALL: 0}; order = [ALL]; adj = {}
    i = 0
    while i < len(order):
        S = order[i]; i += 1
        es = edges(S)
        adj[S] = [T for (lab, T) in es]
        for (lab, T) in es:
            if T not in verts:
                verts[T] = len(order); order.append(T)
                if len(order) > max_states: return None, len(order), None
    # Tarjan SCC (iterative)
    index = {}; low = {}; onst = set(); st = []; sccs = []; idx = 0
    for v0 in order:
        if v0 in index: continue
        work = [(v0, iter(adj[v0]))]; index[v0] = low[v0] = idx; idx += 1; st.append(v0); onst.add(v0)
        while work:
            v, it = work[-1]; adv = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = idx; idx += 1; st.append(w); onst.add(w); work.append((w, iter(adj[w]))); adv = True; break
                elif w in onst: low[v] = min(low[v], index[w])
            if adv: continue
            work.pop()
            if work: u = work[-1][0]; low[u] = min(low[u], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); onst.discard(w); comp.append(w)
                    if w == v: break
                sccs.append(comp)
    ok = True; info = []
    for comp in sccs:
        cs = set(comp)
        ne = sum(1 for v in comp for w in adj[v] if w in cs)
        if ne == 0: continue
        info.append((len(comp), ne))
        if ne != len(comp): ok = False
    return ok, len(order), info
if __name__ == '__main__':
    K = int(sys.argv[1])
    for s in sys.argv[2:]:
        ok, n, info = certify([int(ch) for ch in s], K)
        print(f"{s}: K={K} certified={ok} vertices={n} recurrent(size,edges)={info}")
