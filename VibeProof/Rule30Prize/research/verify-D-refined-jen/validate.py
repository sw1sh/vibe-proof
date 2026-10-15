# Validate right_run / left_run against a full rule-30 simulation from a single black cell.
import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-D-refined-jen')
from halves_lib import right_run, left_run
N = 400; T0 = 50
# full simulation: dict of rows, positions -N..N
rows = []
cur = {0: 1}
def get(r, p): return r.get(p, 0)
for t in range(N + 1):
    rows.append(cur)
    nxt = {}
    for p in range(-t - 1, t + 2):
        v = get(cur, p - 1) ^ (get(cur, p) | get(cur, p + 1))
        if v: nxt[p] = 1
    cur = nxt
c = [get(rows[t], 0) for t in range(N + 1)]
cf = lambda t: c[T0 + t]
# right state at T0: bit k <-> p = k+1, width T0 (rightmost possible black at p = T0)
rs = sum(get(rows[T0], k + 1) << k for k in range(T0))
ls = sum(get(rows[T0], -k - 1) << k for k in range(T0))
steps = N - T0 - 1
y = right_run(rs, T0, cf, steps)
x = left_run(ls, T0, cf, steps)
print("right col1 matches real:", all(y[t] == get(rows[T0 + t], 1) for t in range(steps)))
print("left col-1 matches real:", all(x[t] == get(rows[T0 + t], -1) for t in range(steps)))
print("consistency x = c(t+1) xor (c(t) or y(t)) matches real col -1:",
      all((c[T0 + t + 1] ^ (c[T0 + t] | y[t])) == get(rows[T0 + t], -1) for t in range(steps)))
