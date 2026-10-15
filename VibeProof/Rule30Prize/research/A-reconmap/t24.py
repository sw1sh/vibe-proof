# Are all patterns achievable in every short window [a, a+l-1]? (local forced relations of any kind)
import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1]); lmax = int(sys.argv[2])
ALL, F, L = L_sliced(m)
n = len(L)
res = {}
for l in range(1, lmax + 1):
    bad = []
    for a in range(1, n - l + 2):
        # count achievable patterns of L(a..a+l-1)
        pats = 0
        for p in range(1 << l):
            Z = ALL
            for i in range(l):
                v = L[a - 1 + i]
                Z &= v if (p >> i) & 1 else ~v
                if not Z: break
            if Z & ALL: pats += 1
        if pats < (1 << l): bad.append((a, pats))
    print('l=%d: windows (a, #achievable) with missing patterns:' % l, bad)
