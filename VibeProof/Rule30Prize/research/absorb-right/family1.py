# Theorem B' (1-runs): find minimal j0 such that, for every configuration whose prefix (columns 1..2*j0)
# is (01)^j0, the column-1 values during driver u followed by 1^9 are determined (independent of the tail).
# Then 1^r u is uniformly absorbing for all r >= max(9*j0, 9)  [Lemma A* + Lemma A].
import sys, time
sys.path.insert(0, '.')
from ellabs import solve
from satper import cone_cnf

def determined(u, j0):
    w = u + '1' * 9
    n = len(w)          # need column 1 at times 0..n-1 (driver steps 0..n-2 determine times 1..n-1)
    # cone of (n-1, 1)
    cnt, clauses, v = cone_cnf(w, n - 1, 1, 0)
    base = []
    for i in range(1, 2 * j0 + 1):
        if i > n: break   # columns beyond the cone are irrelevant
        bit = 0 if i % 2 == 1 else 1
        base.append([v(0, i)] if bit else [-v(0, i)])
    for t in range(n):
        x = v(t, 1)
        s0 = solve(cnt[0], clauses, base + [[-x]]) is not None
        s1 = solve(cnt[0], clauses, base + [[x]]) is not None
        if s0 and s1: return False
    return True

def min_j0(u, jmax=40):
    for j0 in range(0, jmax + 1):
        if determined(u, j0): return j0
    return None

if __name__ == '__main__':
    for u in sys.argv[1:]:
        t0 = time.time(); j0 = min_j0(u)
        print(f"u={u}: j0={j0} -> 1^r u uniformly absorbing for r >= {max(9*j0, 9) if j0 is not None else None}  (crude bound {9*((len(u)+10)//2)})  {time.time()-t0:.1f}s", flush=True)
