import sys
sys.path.insert(0, '.')
from core import *
from t8 import step, window_profile
def survivors_hist(a, b):
    states = {(0, 0): ()}
    for k in range(0, b):
        new = {}
        ys = (1,) if k % 2 == 0 else (0, 1)
        for (Dkm1, Dk), h in states.items():
            for yk in ys:
                Dn = step(Dkm1, Dk, k, yk)
                if k + 1 >= a and (Dn & 1): continue
                new.setdefault((Dk, Dn), h + (yk,))
        states = new
    return list(states.values())
for a in range(20, 41):
    b, prof = window_profile(a, 4 * a + 40)
    hs = survivors_hist(a, b - 1)
    for h in hs:
        L = recon_y(list(h))
        f = [h[2 * s + 1] for s in range(len(h) // 2)]
        print('a=%d B=%d L[1..a-1]=%s  f=%s' % (a, b, ''.join(map(str, L[:a - 1])), ''.join(map(str, f))))
