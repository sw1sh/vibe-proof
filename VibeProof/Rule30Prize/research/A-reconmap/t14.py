# Forced cells and simple relations at even and odd times, free f vs golden-mean f.
import sys
sys.path.insert(0, '.')
from core import *
m = int(sys.argv[1])
ALL, F, L = L_sliced(m)
n = len(L)
G = ALL
for i in range(m - 1): G &= (F[i] | F[i + 1])
# odd-time row: F(L)(k) = L(k+1) xor (L(k) or L(k-1)), valid for k+1 <= n
L0 = [0] + L   # L0[k] = L(k), L0[0] = 0
FL = [None] + [L0[k + 1] ^ (L0[k] | L0[k - 1]) for k in range(1, n)]
for name, mask in (('free', ALL), ('golden', G)):
    ce = [(k, 1 if (L0[k] & mask) == mask else 0) for k in range(1, n + 1) if (L0[k] & mask) in (0, mask)]
    co = [(k, 1 if (FL[k] & mask) == mask else 0) for k in range(1, n) if (FL[k] & mask) in (0, mask)]
    print(name, 'even-time forced:', ce)
    print(name, 'odd-time forced:', co)
    # pairwise equalities among even-time cells
    pe = []
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            d = (L0[i] ^ L0[j]) & mask
            if d == 0: pe.append((i, j, '='))
            elif d == mask: pe.append((i, j, '!'))
    po = []
    for i in range(1, n):
        for j in range(i + 1, n):
            d = (FL[i] ^ FL[j]) & mask
            if d == 0: po.append((i, j, '='))
            elif d == mask: po.append((i, j, '!'))
    print(name, 'even-time pair relations:', pe)
    print(name, 'odd-time pair relations:', po)
