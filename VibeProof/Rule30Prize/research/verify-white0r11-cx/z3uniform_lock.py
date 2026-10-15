# Uniform (all initial right-half configurations) z3 checks of the two-period lock for 0^r 11, r >= 10:
#  (A) class(0) != r+2  ==>  x(2Q,1) = 1          (expect UNSAT for the negation)
#  (B) x(0,1) = 1      ==>  x(Q,1) = 1 and column 1 over [0,Q) = 1^(r+1) 0
#  (C) class(0) == r+2 ==>  column 1 over [0,Q) = 0^(r+1) 1
#  plus: is class r+2 at time 0 compatible with x(2Q,1) = 0 ? (shows the Z2 exception is genuinely needed or not)
import sys
from z3 import Bool, BoolVal, Xor, Or, And, Not, Solver, sat, unsat

def build(w, N):
    P = len(w); X = {}
    def x(t, p):
        if p == 0: return BoolVal(w[t % P] == '1')
        if (t, p) not in X: X[(t, p)] = Bool(f"x_{t}_{p}")
        return X[(t, p)]
    s = Solver()
    for t in range(N):
        for p in range(1, N - t + 1):
            s.add(x(t + 1, p) == Xor(x(t, p - 1), Or(x(t, p), x(t, p + 1))))
    return s, x

for r in range(9, 17):
    w = '0' * r + '11'; Q = r + 2; N = 2 * Q
    s, x = build(w, N)
    z2 = And([Not(x(0, p)) for p in range(1, r + 3)] + [x(0, r + 3)])
    s.push(); s.add(Not(z2)); s.add(Not(x(N, 1))); A = s.check(); s.pop()
    s.push(); s.add(x(0, 1)); s.add(Or([x(i, 1) != BoolVal(i <= r) for i in range(Q)] + [Not(x(Q, 1))])); B = s.check(); s.pop()
    s.push(); s.add(z2); s.add(Or([x(i, 1) != BoolVal(i == r + 1) for i in range(Q)])); C = s.check(); s.pop()
    s.push(); s.add(z2); s.add(Not(x(N, 1))); D = s.check(); s.pop()
    print(f"r={r}: (A) non-Z2 & no lock at 2Q: {A}; (B) lock breaks/pattern: {B}; (C) Z2 pattern wrong: {C}; Z2 & no lock at 2Q: {D}", flush=True)
