# Myhill-Nerode style: number of distinct "future behaviours" of prefixes f_0..f_{s-1}:
# future map g -> (L(2s+2), ..., L(2s+1+2h)) for continuations g in {0,1}^h.
import sys, itertools
sys.path.insert(0, '.')
from core import *
from t8 import step
def states_after(prefix):
    y = []
    for b in prefix: y += [1, b]
    Dkm1, Dk = 0, 0
    for k, yk in enumerate(y):
        Dn = step(Dkm1, Dk, k, yk)
        Dkm1, Dk = Dk, Dn
    return Dkm1, Dk, len(y)
def future(prefix, h):
    Dkm1, Dk, k0 = states_after(prefix)
    out = []
    for g in itertools.product((0, 1), repeat=h):
        a, b, k = Dkm1, Dk, k0
        o = 0
        for gb in g:
            for yk in (1, gb):
                Dn = step(a, b, k, yk); a, b = b, Dn; k += 1
                o = (o << 1) | (Dn & 1)
        # one more forced 1 to get the odd depth after last g
        Dn = step(a, b, k, 1); o = (o << 1) | (Dn & 1)
        out.append(o)
    return tuple(out)
for h in (2, 4, 6, 8):
    row = []
    for s in range(0, 13):
        fut = set()
        for p in itertools.product((0, 1), repeat=s):
            fut.add(future(list(p), h))
        row.append(len(fut))
    print('h=%d: distinct futures by prefix length s=0..12:' % h, row, flush=True)
