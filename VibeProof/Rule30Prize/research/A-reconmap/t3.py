import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1])
ALL, E, Fs, L = L_sliced_even(m)
# checks
for s in range(m):
    assert L[2 * s + 1] == E[s]
# consistency with f-sliced recon: compute L_of_f for random e and compare
import random
for trial in range(50):
    idx = random.getrandbits(m)
    f = [(Fs[s] >> idx) & 1 for s in range(m)]
    Lf = L_of_f(f)
    for k in range(1, 2 * m + 2):
        assert Lf[k - 1] == (L[k - 1] >> idx) & 1
print('consistent')
names = ['e%d' % i for i in range(m)]
for s in range(m):
    k = 2 * s + 3
    if k - 1 >= len(L): break
    mons = anf(L[k - 1], m)
    deg = max(bin(x).count('1') for x in mons) if mons else 0
    txt = ' + '.join(mono_str(x, names) for x in sorted(mons, key=lambda x: (bin(x).count('1'), x)))
    print('L(%d): deg %d, %d terms: %s' % (k, deg, len(mons), txt if len(mons) < 40 else txt[:300] + '...'))
