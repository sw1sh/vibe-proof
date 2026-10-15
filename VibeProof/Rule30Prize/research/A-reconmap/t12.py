import sys, itertools
sys.path.insert(0, '.')
from core import *
def tail_info(L, P_max=400):
    n = len(L)
    best = None
    for p in range(1, P_max + 1):
        # minimal preperiod with period p, scanning from the end
        i = n - p - 1
        while i >= 0 and L[i] == L[i + p]: i -= 1
        start = i + 1
        if start <= n - 3 * p and n - start >= 600:   # at least 600 periodic entries and >= 3 periods
            return p, start, ''.join(map(str, L[start:start + min(p, 70)]))
    return None
NN = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
for per in range(1, 8):
    for w in itertools.product((0, 1), repeat=per):
        if any(per % d == 0 and w == w[:d] * (per // d) for d in range(1, per)): continue
        f = (list(w) * (NN // per + 1))[:NN]
        L = L_of_f(f)
        ti = tail_info(L)
        print(''.join(map(str, w)), '->', ti)
