# For periodic f, the row Phi(f) is temporally periodic (F^{2p} = id on it) and spatially eventually periodic.
# Check whether its spatial tail has a "wall": a column that is black at all times of the temporal cycle.
import sys, itertools
sys.path.insert(0, '.')
from core import *
def tail_period(L, start, pmax=400):
    n = len(L)
    for p in range(1, pmax):
        if all(L[i] == L[i + p] for i in range(start, n - p)): return p
    return None
for per in range(1, 7):
    for w in itertools.product((0, 1), repeat=per):
        if any(per % d == 0 and w == w[:d] * (per // d) for d in range(1, per)): continue
        N = 3000
        f = (list(w) * (N // per + 1))[:N]
        L = L_of_f(f)
        rows = forward(L[:4000], 2 * per)    # one full temporal cycle (F^{2 per})
        # look at positions 1000..2000 (inside the periodic tail, far from the truncated end)
        lo, hi = 1000, 2000
        p = tail_period(L[:4000], lo)
        if p is None: print(''.join(map(str, w)), 'no tail period found'); continue
        always_black = [k for k in range(lo, lo + p) if all(r[k] for r in rows[:2 * per])]
        always_white = [k for k in range(lo, lo + p) if not any(r[k] for r in rows[:2 * per])]
        print('f=(%s)^inf: tail period %d, temporal period %d, always-black columns per spatial period: %d, always-white: %d' % (''.join(map(str, w)), p, 2 * per, len(always_black), len(always_white)))
