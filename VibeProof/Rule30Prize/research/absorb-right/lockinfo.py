# Determine the locked layer for word w (from a long simulation): per-phase constant cells.
import sys, random
sys.path.insert(0, '.')
from sim import *
def lock_table(w, phase, width, seed, steps, ncols, Q, tstart):
    random.seed(seed)
    row = random.getrandbits(width) if width > 0 else 0
    wb = [int(ch) for ch in w]; L = len(wb)
    cnt = [[[0,0] for r in range(Q)] for j in range(ncols)]
    for t in range(steps):
        if t >= tstart:
            for j in range(ncols):
                cnt[j][t % Q][(row >> j) & 1] += 1
        c = wb[(phase + t) % L]
        row = ((row << 1) | c) ^ (row | (row >> 1))
    tab = []
    for j in range(ncols):
        s = ''
        for r in range(Q):
            a, b = cnt[j][r]
            s += '0' if b == 0 else ('1' if a == 0 else '*')
        tab.append(s)
    return tab
if __name__ == '__main__':
    w = sys.argv[1]; Q = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    tab = lock_table(w, 0, 1000, seed, 20000, 30, Q, 6000)
    print("col  " + ''.join(str(r % 10) for r in range(Q)))
    for j, s in enumerate(tab): print(f"{j+1:3d}  {s}")
