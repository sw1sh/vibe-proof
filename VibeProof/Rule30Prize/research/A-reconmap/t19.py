import sys, itertools
sys.path.insert(0, '.')
from core import *
def damage(f, i=0):
    g = f[:]; g[i] ^= 1
    A = L_of_f(f); B = L_of_f(g)
    return [k + 1 for k in range(len(A)) if A[k] != B[k]]
N = 300
for w in ['1', '0', '01', '10', '001', '011', '0001', '0111', '00111', '01011']:
    f = (list(map(int, w)) * N)[:N]
    d = damage(f)
    print(w, 'damage count', len(d), 'max', max(d), 'first', d[:12])
