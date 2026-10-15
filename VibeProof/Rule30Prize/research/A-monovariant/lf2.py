import sys
sys.path.insert(0, '.')
from lf import Lof, col, s
n = 120
def defects(L):
    return ''.join('x' if (L[k-1] != (k % 2)) else '.' for k in range(1, len(L)+1))
for f in ([0] + [1]*n, [1,0] + [1]*n, [1,1,0] + [1]*n, [1,1,1,0]+[1]*n, [0,0]+[1]*n, [0,1,0]+[1]*n, [1]*5+[0]+[1]*5+[0]+[1]*n):
    L = Lof(col(f[:n]))
    print('f=' + s(f[:16]) + '...')
    print('  L      =' + s(L[:110]))
    print('  defects=' + defects(L[:110]))
