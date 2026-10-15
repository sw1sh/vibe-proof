# Sparse forced sets: pairs/triples {i,j(,k)} (positions up to 33) such that L is never 0 on all of them.
import sys, itertools
sys.path.insert(0, '.')
from core import *
m = 16
ALL, F, L = L_sliced(m)
n = len(L)
Z = [(~L[k]) & ALL for k in range(n)]   # truth table of L(k+1) = 0
pairs = [(i + 1, j + 1) for i in range(n) for j in range(i + 1, n) if (Z[i] & Z[j]) == 0]
print('forced pairs (L_i or L_j = 1):', pairs)
trip = []
for i in range(n):
    for j in range(i + 1, n):
        zij = Z[i] & Z[j]
        if zij == 0: continue
        for k in range(j + 1, n):
            if (zij & Z[k]) == 0 and not any((Z[a] & Z[b]) == 0 for a, b in ((i, k), (j, k))):
                trip.append((i + 1, j + 1, k + 1))
print('forced triples (no forced sub-pair):', len(trip), trip[:40])
print('max smallest element among forced triples:', max(t[0] for t in trip) if trip else None)
