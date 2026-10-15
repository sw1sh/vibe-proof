# Is the left regular region independent of the driver?  Left half p<=-1 driven by column 0 = c'.
# bit i <-> p = -(i+1).  Compare true left half with left halves driven by other drivers.
import sys, random
def true_rows(N):
    rows = []; row = 1 << N
    for t in range(N):
        rows.append(row); row = (row << 1) ^ (row | (row >> 1))
    return rows
def left_rows(cvals):
    row = 0; rows = []
    for t, ct in enumerate(cvals):
        rows.append(row)
        W = t + 2; mask = (1 << W) - 1
        right = ((row << 1) | ct) & mask
        left = row >> 1
        row = (left ^ (row | right)) & mask
    return rows
N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
TR = true_rows(N)
center = [(r >> N) & 1 for r in TR]
# true left half as bit i <-> p=-(i+1): extract bits N-1, N-2, ... -> reverse
def true_left(r, t):
    # positions -1..-t : bits N-1 down to N-t
    seg = (r >> (N - t)) & ((1 << t) - 1)   # bit 0 <-> p=-t ... bit t-1 <-> p=-1
    return int(bin(seg)[2:].zfill(t)[::-1], 2) if t > 0 else 0
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
mode = sys.argv[3] if len(sys.argv) > 3 else 'random'
if mode == 'random':
    drv = [1] + [random.getrandbits(1) for _ in range(N - 1)]
elif mode == 'zero':
    drv = [1] + [0] * (N - 1)
elif mode.startswith('per:'):
    w = mode[4:]; drv = [1] + [int(w[(t - 1) % len(w)]) for t in range(1, N)]
elif mode.startswith('flip:'):
    s = int(mode[5:]); drv = center[:]; drv[s] ^= 1
LR = left_rows(drv)
# for each t, leftmost position (most negative p) where they differ
out = []
for t in range(1, N, N // 20):
    tl = true_left(TR[t], t); ll = LR[t]
    d = tl ^ ll
    if d == 0: out.append((t, None)); continue
    i = d.bit_length() - 1   # largest i -> most negative p = -(i+1)
    out.append((t, -(i + 1), round(-(i + 1) / t, 3)))
print(mode, out)
