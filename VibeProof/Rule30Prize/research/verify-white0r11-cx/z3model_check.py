# Validate the z3 encoding semantics: extract a model where x(n,1) != x(n+Q,1) and replay it by direct simulation.
import sys
from z3 import Bool, BoolVal, Xor, Or, Solver, sat, is_true

def model_cx(w, n, Q):
    N = n + Q; P = len(w); X = {}
    def x(t, p):
        if p == 0: return BoolVal(w[t % P] == '1')
        if (t, p) not in X: X[(t, p)] = Bool(f"x_{t}_{p}")
        return X[(t, p)]
    s = Solver()
    for t in range(N):
        for p in range(1, N - t + 1):
            s.add(x(t + 1, p) == Xor(x(t, p - 1), Or(x(t, p), x(t, p + 1))))
    s.add(Xor(x(n, 1), x(N, 1)))
    if s.check() != sat: return None
    m = s.model()
    init = [1 if is_true(m.eval(x(0, p), model_completion=True)) else 0 for p in range(1, N + 2)]
    return init

def sim_col1(w, init, steps):
    P = len(w); row = list(init) + [0] * (steps + 3); out = []
    for t in range(steps + 1):
        out.append(row[0])
        d = int(w[t % P]); ext = row + [0]
        row = [ (d if p == 0 else ext[p - 1]) ^ (ext[p] | ext[p + 1]) for p in range(len(row)) ]
    return out

for w, n, Q in [("00000011", 32, 16), ("000000011", 40, 18), ("000000011", 60, 18)]:
    init = model_cx(w, n, Q)
    if init is None: print(w, n, Q, "no model (forced)"); continue
    col = sim_col1(w, init, n + Q)
    print(w, n, Q, "model replay: x(n,1)=", col[n], "x(n+Q,1)=", col[n + Q], "differ" if col[n] != col[n + Q] else "SAME (encoding bug!)")
