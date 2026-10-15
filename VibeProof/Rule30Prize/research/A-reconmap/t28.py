import sys
sys.path.insert(0, '.')
from core import *
from t18 import survivors_hist
from t8 import window_profile
def zero_runs(L, minlen=6):
    runs = []; i = 0
    while i < len(L):
        if L[i] == 0:
            j = i
            while j < len(L) and L[j] == 0: j += 1
            if j - i >= minlen: runs.append((i + 1, j))
            i = j
        else: i += 1
    return runs
for a in (12, 20, 28, 32, 39, 40):
    b, prof = window_profile(a, 4 * a + 40)
    for h in survivors_hist(a, b - 1)[:2]:
        f = [h[2 * s + 1] for s in range(len(h) // 2)]
        L = recon_y(list(h))
        out = []
        for name, g in (('even', f[0::2]), ('odd', f[1::2]), ('double', [x for x in f for _ in (0, 1)])):
            Lg = L_of_f(g)
            out.append('%s: zero runs %s' % (name, zero_runs(Lg)))
        print('a=%d B=%d f=%s  own zero runs %s | %s' % (a, b, ''.join(map(str, f)), zero_runs(L), ' ; '.join(out)))
