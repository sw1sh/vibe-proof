import sys
sys.path.insert(0, '.')
from core import *
N = 1500
f = ([1, 0] * N)[:N]
g = f[:]; g[0] ^= 1
A = L_of_f(f); B = L_of_f(g)
d = [A[k] ^ B[k] for k in range(len(A))]
# period of the damage sequence in the second half
tail = d[1000:2900]
for p in range(1, 200):
    if all(tail[i] == tail[i + p] for i in range(len(tail) - p)):
        print('damage sequence eventually periodic with period', p, 'pattern', ''.join(map(str, tail[:p])), 'ones per period', sum(tail[:p])); break
print('Phi((10)^inf) tail:', ''.join(map(str, A[2000:2014])), ' Phi(0(01)^inf) tail:', ''.join(map(str, B[2000:2028])))
