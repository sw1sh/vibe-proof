# Local automaton: state (t mod P, x_1..x_m); x_{m+1} is adversarial (free).  Find terminal SCCs
# (closed under all choices) and report those on which column 1 is forced periodic.
import itertools, sys
exec(open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/gf2-algebra/forcing.py').read().split('def primitive_words')[0])
def traps(w, m):
    P = len(w)
    nodes = [(ph, xs) for ph in range(P) for xs in itertools.product((0, 1), repeat=m)]
    edges = {v: step_det(w, *v) for v in nodes}
    comps = sccs(nodes, edges)
    compid = {}
    for i, c in enumerate(comps):
        for v in c: compid[v] = i
    out = []
    for i, comp in enumerate(comps):
        cs = set(comp)
        if any(u not in cs for v in comp for u in edges[v]): continue  # not terminal
        # periodic col_1 within comp?
        lab = {v: v[1][0] for v in comp}
        s0 = comp[0]; path = [s0]; seen = {s0: 0}; cur = s0
        while True:
            nx = edges[cur][0]
            if nx in seen: break
            seen[nx] = len(path); path.append(nx); cur = nx
        cyc = path[seen[nx]:]; u = [lab[s] for s in cyc]; q = len(u)
        for d in range(1, q + 1):
            if q % d == 0 and all(u[k] == u[k % d] for k in range(q)): u = u[:d]; q = d; break
        phase = {cyc[0]: 0}; stack = [cyc[0]]; ok = True
        while stack and ok:
            s = stack.pop(); f = phase[s]
            if lab[s] != u[f]: ok = False; break
            for v in edges[s]:
                g = (f + 1) % q
                if v in phase:
                    if phase[v] != g: ok = False; break
                else: phase[v] = g; stack.append(v)
        out.append((len(comp), ok, ''.join(map(str, u)) if ok else None))
    return out
for w in sys.argv[1:]:
    for m in range(1, 13):
        tr = traps([int(ch) for ch in w], m)
        good = [t for t in tr if t[1]]
        print("w=%s m=%2d: %d terminal SCCs, sizes %s; with periodic col1: %s" % (w, m, len(tr), [t[0] for t in tr][:6], good[:3]))
        if good: break
