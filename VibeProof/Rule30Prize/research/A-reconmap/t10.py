import sys
sys.path.insert(0, '.')
from core import *
Ls = sys.argv[1]
steps = int(sys.argv[2])
L = [int(ch) for ch in Ls]
rows = forward(L, steps)
for t, r in enumerate(rows):
    s = ''.join('#' if v else '.' for v in r[:110])
    print('%3d %s %s' % (t, 'y=%d' % r[0], s))
