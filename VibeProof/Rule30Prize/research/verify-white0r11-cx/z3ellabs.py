# Independent re-implementation (z3, own encoding, own SCC code) of the "leftmost-1" abstraction test.
# Classes at a phase-0 time: c in 0..L = (columns 1..c white, column c+1 black); L+1 = (columns 1..L+1 white).
# For each class: possible column-1 words over one period, possible classes one period later.
import sys, time
from z3 import Bool, BoolVal, Xor, Or, Not, Solver, sat, unsat, is_true, And

def analyze(w, L):
    P = len(w); X = {}
    def x(t, p):
        if p == 0: return BoolVal(w[t % P] == '1')
        if (t, p) not in X: X[(t, p)] = Bool(f"x_{t}_{p}")
        return X[(t, p)]
    top = L + 1 + P  # columns at time 0
    s = Solver()
    for t in range(P):
        for p in range(1, top - (t + 1) + 1):  # cell (t+1,p) for p <= top - (t+1)
            s.add(x(t + 1, p) == Xor(x(t, p - 1), Or(x(t, p), x(t, p + 1))))
    def cls(t, c):
        if c <= L: return [Not(x(t, p)) for p in range(1, c + 1)] + [x(t, c + 1)]
        return [Not(x(t, p)) for p in range(1, L + 2)]
    nodes = {}
    for c in range(L + 2):
        s.push(); s.add(*cls(0, c))
        outs = set()
        while True:
            if s.check() != sat: break
            m = s.model()
            o = tuple(1 if is_true(m.eval(x(t, 1), model_completion=True)) else 0 for t in range(P))
            outs.add(o)
            s.add(Or([Not(x(t, 1)) if o[t] else x(t, 1) for t in range(P)]))
            if len(outs) > 16: break
        s.pop()
        nexts = set()
        for c2 in range(L + 2):
            s.push(); s.add(*cls(0, c)); s.add(*cls(P, c2))
            if s.check() == sat: nexts.add(c2)
            s.pop()
        nodes[c] = (outs, nexts)
    return nodes

def scc_ok(nodes):
    keys = list(nodes)
    reach = {u: set(nodes[u][1]) for u in keys}
    changed = True
    while changed:
        changed = False
        for u in keys:
            new = set(reach[u])
            for v in list(reach[u]): new |= reach[v]
            if new != reach[u]: reach[u] = new; changed = True
    ok = True; comps = []
    seen = set()
    for u in keys:
        if u in reach[u] and u not in seen:
            comp = sorted(v for v in keys if v in reach[u] and u in reach[v])
            seen |= set(comp)
            outs = set()
            for v in comp: outs |= nodes[v][0]
            comps.append((comp, sorted(''.join(map(str, o)) for o in outs)))
            if len(outs) != 1: ok = False
    return ok, comps

if __name__ == '__main__':
    r = int(sys.argv[1]); extra = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    w = '0' * r + '11'; L = len(w) + extra
    t0 = time.time()
    nodes = analyze(w, L)
    ok, comps = scc_ok(nodes)
    for c in sorted(nodes):
        print(f"  class {c if c <= L else '>'+str(L)}: outs {sorted(''.join(map(str,o)) for o in nodes[c][0])} next {sorted(nodes[c][1])}")
    print(f"r={r} w={w} L={L}: {'PASS' if ok else 'FAIL'}  nontrivial SCCs: {comps}  ({time.time()-t0:.1f}s)", flush=True)
