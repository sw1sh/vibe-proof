import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1])
ALL, F, L = L_sliced(m)
n = len(L)
G = ALL
for i in range(m - 1):
    G &= (F[i] | F[i + 1])       # golden mean: no two consecutive zeros
print('golden-mean assignments:', bin(G).count('1'), 'of', 1 << m)
def relations(vecs, mask):
    basis = []; rels = []
    for name, v in vecs:
        v &= mask
        combo = {name}
        for (pb, bv, bc) in basis:
            if (v >> pb) & 1:
                v ^= bv; combo ^= bc
        if v == 0: rels.append(sorted(combo, key=lambda s: (len(s), s)))
        else: basis.append((v.bit_length() - 1, v, combo))
    return rels
vecs = [('1', ALL)] + [('L%d' % (k + 1), L[k]) for k in range(n)]
for r in relations(vecs, G): print('  ', ' + '.join(r), '= 0')
# forced windows under golden mean
res = []
for a in range(1, n + 1):
    Z = G; b = None
    for k in range(a, n + 1):
        Z &= ~L[k - 1]
        if Z == 0: b = k; break
    res.append((a, b))
print('golden B(a):', res)
