import sys, random
sys.path.insert(0, '.')
from core import *
random.seed(5)
m = 200
stats = []
for trial in range(30):
    f = [random.getrandbits(1) for _ in range(m)]
    L0 = L_of_f(f)
    g = f[:]; g[0] ^= 1
    L1 = L_of_f(g)
    diff = [k + 1 for k in range(len(L0)) if L0[k] != L1[k]]
    stats.append((len(diff), max(diff)))
    if trial < 10: print(diff[:30], '... count', len(diff), 'max', max(diff))
print(stats)
