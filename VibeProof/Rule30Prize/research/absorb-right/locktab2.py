# Find a run that locks (column 1 periodic) and print the per-phase table of the locked layer.
import sys, random
sys.path.insert(0, '.')
w = sys.argv[1]; Q = int(sys.argv[2]); width = int(sys.argv[3]); steps = int(sys.argv[4]); ncols = int(sys.argv[5])
wb = [int(ch) for ch in w]; P = len(wb)
for seed in range(1, 200):
    random.seed(seed)
    row = random.getrandbits(width)
    hist = []
    for t in range(steps):
        hist.append(row & ((1 << ncols) - 1))
        row = ((row << 1) | wb[t % P]) ^ (row | (row >> 1))
    col1 = [h & 1 for h in hist]
    # periodic over last half?
    h2 = steps // 2
    if all(col1[t] == col1[t + Q] for t in range(h2, steps - Q)):
        # find start of periodicity
        T = h2
        while T > 0 and col1[T - 1] == col1[T - 1 + Q]: T -= 1
        print("seed", seed, "col1 periodic from", T)
        tstart = max(T + 200, h2)
        tstart -= tstart % Q   # align with phase 0 of Q (driver phase = t mod P, Q multiple of P)
        print("col  " + ''.join(str(r % 10) for r in range(Q)))
        for j in range(ncols):
            s = ''
            for r in range(Q):
                vals = set((hist[t] >> j) & 1 for t in range(tstart + r, steps, Q))
                s += '*' if len(vals) > 1 else str(vals.pop())
            print(f"{j+1:3d}  {s}")
        break
