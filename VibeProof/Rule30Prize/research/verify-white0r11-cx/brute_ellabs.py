# SAT-free exhaustive computation of the leftmost-1 abstraction graph (all 2^W cone bases), numpy vectorized.
import sys, time
import numpy as np

def classes(R, L):
    # class = index of first 1 among bits 0..L (column = index+1), else L+1
    cls = np.full(R.shape, L + 1, dtype=np.int64)
    for i in range(L, -1, -1):
        cls = np.where((R >> np.uint64(i)) & np.uint64(1) == 1, i, cls)
    return cls

def analyze(r, L):
    w = [0] * r + [1, 1]; P = len(w); W = L + 1 + P
    X = np.arange(1 << W, dtype=np.uint64)
    mask = np.uint64((1 << W) - 1)
    R = X.copy()
    out = np.zeros(X.shape, dtype=np.uint64)
    for t in range(P):
        out = (out << np.uint64(1)) | (R & np.uint64(1))
        R = (((R << np.uint64(1)) | np.uint64(w[t])) ^ (R | (R >> np.uint64(1)))) & mask
    c0 = classes(X, L); c1 = classes(R, L)
    nodes = {}
    for c in range(L + 2):
        sel = c0 == c
        outs = set(int(o) for o in np.unique(out[sel]))
        nexts = set(int(n) for n in np.unique(c1[sel]))
        nodes[c] = (outs, nexts)
    return nodes, P

def scc(nodes):
    keys = list(nodes); reach = {u: set(nodes[u][1]) for u in keys}
    ch = True
    while ch:
        ch = False
        for u in keys:
            new = set(reach[u])
            for v in list(reach[u]): new |= reach[v]
            if new != reach[u]: reach[u] = new; ch = True
    comps = []; seen = set(); ok = True
    for u in keys:
        if u in reach[u] and u not in seen:
            comp = sorted(v for v in keys if v in reach[u] and u in reach[v]); seen |= set(comp)
            outs = set()
            for v in comp: outs |= nodes[v][0]
            comps.append((comp, outs)); ok = ok and len(outs) == 1
    return ok, comps

r = int(sys.argv[1]); L = int(sys.argv[2])
t0 = time.time()
nodes, P = analyze(r, L)
ok, comps = scc(nodes)
for c in sorted(nodes):
    print(f"  class {c if c <= L else '>'+str(L)}: outs {[format(o, '0%db' % P) for o in sorted(nodes[c][0])]} next {sorted(nodes[c][1])}")
print(f"r={r} L={L} W={L+1+P}: {'PASS' if ok else 'FAIL'} SCCs {[(c, [format(o, '0%db' % P) for o in s]) for c, s in comps]} ({time.time()-t0:.1f}s)")
