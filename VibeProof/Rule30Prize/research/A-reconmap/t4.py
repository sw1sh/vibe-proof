import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1])
ALL, F, L = L_sliced(m)
names = ['f%d' % i for i in range(m)]
for k in range(1, 2 * m + 2):
    mons = anf(L[k - 1], m)
    deg = max(bin(x).count('1') for x in mons) if mons else 0
    txt = ' + '.join(mono_str(x, names) for x in sorted(mons, key=lambda x: (bin(x).count('1'), x)))
    print('L(%d): deg %d, %d terms: %s' % (k, deg, len(mons), txt if len(mons) < 30 else txt[:250] + '...'))
