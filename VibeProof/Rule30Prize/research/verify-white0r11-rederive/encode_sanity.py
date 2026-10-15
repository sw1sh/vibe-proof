# Sanity check of mycnf.encode: real trajectories satisfy every clause except the query clause.
import random, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-white0r11-rederive')
from mycnf import encode
w = '00000011'; Q = 16; n = 33; N = n + Q; P = len(w)
nv, cls = encode(w, n, Q)
# rebuild the variable numbering exactly as encode does
var = {}
for t in range(N + 1):
    for p in range(1, 2 + N - t): var[(t, p)] = len(var) + 1
rnd = random.Random(7)
for trial in range(200):
    cols = N + 2
    x = {}
    for p in range(1, cols + 1): x[(0, p)] = rnd.randint(0, 1)
    d = [int(ch) for ch in w]
    for t in range(1, N + 1):
        for p in range(1, cols + 1 - t):
            left = d[(t - 1) % P] if p == 1 else x[(t - 1, p - 1)]
            x[(t, p)] = left ^ (x[(t - 1, p)] | x[(t - 1, p + 1)])
    # assignment: cell vars, then aux vars in creation order
    val = {}
    for (t, p), k in var.items(): val[k] = x[(t, p)]
    k = len(var)
    for t in range(1, N + 1):
        for p in range(1, 2 + N - t):
            k += 1; val[k] = x[(t - 1, p)] | x[(t - 1, p + 1)]
    unsat = [c for c in cls[:-2] if not any((val[abs(l)] == 1) == (l > 0) for l in c)]
    assert not unsat, (trial, unsat[:3])
    assert x[(n, 1)] == x[(N, 1)], ("period violated in simulation", trial)
print("200 random trajectories satisfy all non-query clauses; x(n,1)=x(n+Q,1) holds in each")
