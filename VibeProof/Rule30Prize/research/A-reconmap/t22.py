# The 2-adic map G: even-depth values e (e_s = L(2s+2)) -> odd-depth values (L(2s+3)).
import sys
sys.path.insert(0, '.')
from t17 import L_from_even
def G(e, nbits):
    L, f = L_from_even(e, 2 * nbits + 3)
    return [L[2 * s + 2] for s in range(nbits)]   # L(2s+3)
def bits(n, w):
    return [(n >> i) & 1 for i in range(w)]
NB = 60
for n in list(range(0, 20)):
    g = G(bits(n, NB), NB)
    print('%3d -> %s' % (n, ''.join(map(str, g))))
# G(G(n)) == n ?
neg1 = [1] * NB
print('G(-1) =', ''.join(map(str, G(neg1, NB))))
