# Find all f-prefixes (as y) for which L is zero on [a, b]; print L prefix and f.
import sys
sys.path.insert(0, '.')
from core import *
from t8 import step
def survivors(a, b):
    # states carry the y history
    states = {(0, 0): [()]}
    for k in range(0, b):
        new = {}
        ys = (1,) if k % 2 == 0 else (0, 1)
        for (Dkm1, Dk), hists in states.items():
            for yk in ys:
                Dn = step(Dkm1, Dk, k, yk)
                if k + 1 >= a and (Dn & 1): continue
                key = (Dk, Dn)
                lst = new.setdefault(key, [])
                for h in hists:
                    if len(lst) < 50: lst.append(h + (yk,))
        states = new
    return states
a = int(sys.argv[1]); b = int(sys.argv[2])
st = survivors(a, b)
print('states', len(st))
for key, hs in list(st.items())[:20]:
    for h in hs[:3]:
        f = [h[2 * s + 1] for s in range(len(h) // 2)]
        L = recon_y(list(h))
        print('f=', ''.join(map(str, f)), ' L=', ''.join(map(str, L)))
