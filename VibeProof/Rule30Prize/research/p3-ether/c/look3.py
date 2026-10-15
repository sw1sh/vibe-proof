import sys
w = sys.argv[1]; steps = int(sys.argv[2]); P = int(sys.argv[3]); W = int(sys.argv[4]); t0 = int(sys.argv[5]); cnt = int(sys.argv[6])
row = 0
def cf(t): return 1 if t == 0 else int(w[(t - 1) % len(w)])
for t in range(steps):
    c = cf(t); full = (row << 1) | c
    if t >= t0 and (t - t0) % P == 0 and (t - t0) // P < cnt:
        print(f"{t:6d} " + ''.join('#' if (full >> p) & 1 else '.' for p in range(W)))
    n = t + 3; mask = (1 << n) - 1
    row = ((full & mask) ^ (((full >> 1) & mask) | ((full >> 2) & mask))) & mask
