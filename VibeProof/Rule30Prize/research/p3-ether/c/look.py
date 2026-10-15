# Right half driven by c = 1 then w^inf; print a late window of columns 0..W at successive times.
import sys
w = sys.argv[1]; steps = int(sys.argv[2]); W = int(sys.argv[3]); show = int(sys.argv[4])
row = 0  # bit i <-> p = i+1
def cf(t): return 1 if t == 0 else int(w[(t - 1) % len(w)])
hist = []
for t in range(steps + show):
    c = cf(t)
    full = (row << 1) | c          # bit 0 = column 0
    if t >= steps:
        s = ''.join('#' if (full >> p) & 1 else '.' for p in range(W))
        print(f"{t:6d} ph={(t-1)%len(w)} {s}")
    n = t + 3; mask = (1 << n) - 1
    leftn = full & mask            # old(p-1) for bit i (p=i+1) is bit i of full
    cen = (full >> 1) & mask
    rightn = (full >> 2) & mask
    row = (leftn ^ (cen | rightn)) & mask
