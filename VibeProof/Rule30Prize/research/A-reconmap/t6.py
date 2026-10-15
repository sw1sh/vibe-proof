import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1]); a = int(sys.argv[2]); b = int(sys.argv[3])
ALL, F, L = L_sliced(m)
Z = ALL
for k in range(a, b + 1):
    Z &= ~L[k - 1]
Z &= ALL
idxs = [i for i in range(1 << m) if (Z >> i) & 1]
print('count', len(idxs))
for i in idxs[:40]:
    f = [(i >> s) & 1 for s in range(m)]
    Lf = L_of_f(f)
    print(''.join(map(str, f)), ' L=', ''.join(map(str, Lf)))
