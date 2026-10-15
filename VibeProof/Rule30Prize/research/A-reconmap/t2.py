import sys, time
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1])
t0 = time.time()
ALL, F, L = L_sliced(m)
n = len(L)  # = 2m+1
print('built', m, time.time() - t0)
# window forcing: B(a) = min b with AND_{k=a..b} ~L(k) == 0
res = []
for a in range(1, n + 1):
    Z = ALL
    b = None
    for k in range(a, n + 1):
        Z &= ~L[k - 1] & ALL
        if Z == 0: b = k; break
    res.append((a, b))
print('B(a):', [(a, b) for a, b in res])
print('window lengths:', [(b - a + 1 if b else None) for a, b in res])
