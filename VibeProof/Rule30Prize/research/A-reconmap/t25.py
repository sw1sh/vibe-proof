import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1]); lmax = int(sys.argv[2]); amin = int(sys.argv[3])
ALL, F, L = L_sliced(m)
n = len(L)
for l in range(1, lmax + 1):
    for a in range(amin, n - l + 2):
        miss = []
        for p in range(1 << l):
            Z = ALL
            for i in range(l):
                v = L[a - 1 + i]
                Z &= v if (p >> i) & 1 else ~v
                if not Z: break
            if not (Z & ALL): miss.append(''.join(str((p >> i) & 1) for i in range(l)))
        # report only minimal missing patterns (not implied by a missing sub-pattern in a shorter window)
        if miss: print('l=%d a=%d missing L(a..a+l-1) =' % (l, a), miss)
