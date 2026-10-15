# Independent re-check (z3, own encoding) of the SAT uniform test: for the w-driven right half
# (column 0 = w[t mod P], ALL initial configurations of columns >= 1), is x(n,1) == x(n+Q,1) forced?
import sys
from z3 import Bool, BoolVal, Xor, Or, Solver, unsat, sat, And, Not

def forced(w, n, Q):
    N = n + Q
    P = len(w)
    X = {}
    def x(t, p):
        if p == 0: return BoolVal(w[t % P] == '1')
        if (t, p) not in X: X[(t, p)] = Bool(f"x_{t}_{p}")
        return X[(t, p)]
    s = Solver()
    for t in range(N):
        for p in range(1, N - t + 1):   # cell (t+1, p) inside cone of (N, 1): p <= 1 + N - (t+1)
            s.add(x(t + 1, p) == Xor(x(t, p - 1), Or(x(t, p), x(t, p + 1))))
    s.add(Xor(x(n, 1), x(N, 1)))
    res = s.check()
    return res == unsat

w = sys.argv[1]; Q = int(sys.argv[2]); n0 = int(sys.argv[3]); n1 = int(sys.argv[4])
for n in range(n0, n1):
    print(w, "Q", Q, "n", n, "forced" if forced(w, n, Q) else "NOT forced", flush=True)
