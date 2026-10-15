import sys, itertools
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1])
ALL, F, L = L_sliced(m)
n = len(L)
# affine relations among L(1..n): vectors = [ALL] + L ; find kernel via elimination with tracking
vecs = [('1', ALL)] + [('L%d' % (k + 1), L[k]) for k in range(n)]
basis = []  # list of (pivotbit, vec, combo set)
rels = []
for name, v in vecs:
    combo = {name}
    for (pb, bv, bc) in basis:
        if (v >> pb) & 1:
            v ^= bv; combo ^= bc
    if v == 0:
        rels.append(sorted(combo, key=lambda s: (len(s), s)))
    else:
        pb = v.bit_length() - 1
        basis.append((pb, v, combo))
print('affine relations among 1, L(1..%d):' % n)
for r in rels: print('  ', ' + '.join(r), '= 0')
