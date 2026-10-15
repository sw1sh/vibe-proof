# Local forcing test.  Hypothesis: c(t) = w[t mod P] for all t >= T.
# Unknown right columns x_1..x_m (t >= T) satisfy the exact rule for p < m and, for p = m,
# x_m(t) = 1 => x_m(t+1) = not x_{m-1}(t)  (x_{m+1} unknown).  State at t: (t mod P, x_1..x_m).
# Labels (functions of the state): right columns x_1..x_{m-1}, left columns col_{-1}..col_{-(m)}.
# A label is FORCED eventually periodic if, in every nontrivial SCC, all label sequences are periodic.
# Then c eventually w-periodic => two eventually periodic columns => contradiction (Jen).
import itertools, sys
sys.setrecursionlimit(100000)
def step_det(w, ph, xs):
    # returns list of successor states (ph', xs')
    m = len(xs); P = len(w); c = w[ph]
    full = (c,) + xs
    nxt = []
    for p in range(1, m):   # exact for p < m
        nxt.append(full[p - 1] ^ (full[p] | full[p + 1]))
    outs = []
    if xs[m - 1] == 1:
        outs.append(tuple(nxt) + (1 ^ full[m - 1],))
    else:
        outs.append(tuple(nxt) + (0,)); outs.append(tuple(nxt) + (1,))
    return [((ph + 1) % P, o) for o in outs]
def future_x1(w, ph, xs, n):
    # x_1 at times t..t+n-1 (n <= m), with arbitrary choice for free x_m
    res = []; cur = (ph, xs)
    for j in range(n):
        res.append(cur[1][0]); cur = step_det(w, *cur)[0]
    return res
def labels(w, ph, xs):
    m = len(xs); P = len(w)
    lab = {}
    for p in range(1, m): lab['R%d' % p] = xs[p - 1]
    x1 = future_x1(w, ph, xs, m)
    cseq = [w[(ph + j) % P] for j in range(m + 1)]
    prev2 = None; prev = None
    # col_{-1}(tau) for tau = 0..m-1 (relative)
    col = [cseq[j + 1] ^ (cseq[j] | x1[j]) for j in range(m)]
    lab['L1'] = col[0]
    right = cseq[:m]  # col_0
    k = 1
    while len(col) > 1:
        newcol = [col[j + 1] ^ (col[j] | right[j]) for j in range(len(col) - 1)]
        right = col; col = newcol; k += 1
        lab['L%d' % k] = col[0]
    return lab
def sccs(nodes, edges):
    # iterative Tarjan
    index = {}; low = {}; onst = set(); st = []; out = []; counter = 0
    for root in nodes:
        if root in index: continue
        work = [(root, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                index[v] = low[v] = counter; counter += 1; st.append(v); onst.add(v)
            recurse = False
            succ = edges[v]
            while i < len(succ):
                u = succ[i]; i += 1
                if u not in index:
                    work.append((v, i)); work.append((u, 0)); recurse = True; break
                elif u in onst:
                    low[v] = min(low[v], index[u])
            if recurse: continue
            if low[v] == index[v]:
                comp = []
                while True:
                    u = st.pop(); onst.discard(u); comp.append(u)
                    if u == v: break
                out.append(comp)
            if work:
                p = work[-1][0]; low[p] = min(low[p], low[v])
    return out
def forced(w, m):
    P = len(w)
    nodes = [(ph, xs) for ph in range(P) for xs in itertools.product((0, 1), repeat=m)]
    edges = {v: step_det(w, *v) for v in nodes}
    labs = {v: labels(w, *v) for v in nodes}
    comps = sccs(nodes, edges)
    names = list(labs[nodes[0]].keys())
    result = {}
    for name in names:
        ok = True
        for comp in comps:
            cs = set(comp)
            if len(comp) == 1 and comp[0] not in edges[comp[0]]: continue  # trivial SCC
            # find a cycle label word from comp[0]
            s0 = comp[0]
            # BFS phase assignment with unknown period: follow a cycle first
            path = [s0]; seen = {s0: 0}; cur = s0
            while True:
                nx = [u for u in edges[cur] if u in cs][0]
                if nx in seen: break
                seen[nx] = len(path); path.append(nx); cur = nx
            cyc = path[seen[nx]:]
            u = [labs[s][name] for s in cyc]
            q = len(u)
            for d in range(1, q + 1):
                if q % d == 0 and all(u[i] == u[i % d] for i in range(q)): u = u[:d]; q = d; break
            phase = {cyc[0]: 0}; stack = [cyc[0]]
            while stack and ok:
                s = stack.pop(); f = phase[s]
                if labs[s][name] != u[f]: ok = False; break
                for v in edges[s]:
                    if v not in cs: continue
                    g = (f + 1) % q
                    if v in phase:
                        if phase[v] != g: ok = False; break
                    else: phase[v] = g; stack.append(v)
            if len(phase) < len(cs) and ok:
                # states of comp not reached from cyc[0] cannot happen in an SCC
                ok = False
            if not ok: break
        result[name] = ok
    return result
def primitive_words(P):
    out = set()
    for bits in itertools.product((0, 1), repeat=P):
        if any(P % d == 0 and d < P and all(bits[i] == bits[i % d] for i in range(P)) for d in range(1, P)): continue
        rots = [bits[i:] + bits[:i] for i in range(P)]
        out.add(min(rots))
    return sorted(out)
M = int(sys.argv[1]); PMAX = int(sys.argv[2])
for P in range(1, PMAX + 1):
    for w in primitive_words(P):
        for m in range(1, M + 1):
            r = forced(w, m)
            f = [k for k, v in r.items() if v]
            if f:
                print("w=%s m=%d forced eventually periodic: %s" % (''.join(map(str, w)), m, f)); break
        else:
            print("w=%s: nothing forced up to m=%d" % (''.join(map(str, w)), M))
