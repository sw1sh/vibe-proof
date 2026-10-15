# Left half driven by c' = true c on [0,T) then w^inf. Leftmost position where it differs from the true
# left half (i.e., how far the hypothetical periodic driver's influence has spread).
import sys
N = int(sys.argv[1]); T = int(sys.argv[2]); words = sys.argv[3:]
def true_rows(N):
    rows = []; row = 1 << N
    for t in range(N):
        rows.append(row); row = (row << 1) ^ (row | (row >> 1))
    return rows
TR = true_rows(N)
center = [(r >> N) & 1 for r in TR]
def left_bits(r, t):
    seg = (r >> (N - t)) & ((1 << t) - 1)
    return int(bin(seg)[2:].zfill(t)[::-1], 2) if t > 0 else 0
def left_rows(cvals):
    row = 0; rows = []
    for t, ct in enumerate(cvals):
        rows.append(row)
        W = t + 2; mask = (1 << W) - 1
        right = ((row << 1) | ct) & mask
        row = ((row >> 1) ^ (row | right)) & mask
    return rows
for w in words:
    P = len(w)
    drv = center[:T] + [int(w[(t - T) % P]) for t in range(T, N)]
    LR = left_rows(drv)
    out = []
    for t in range(T, N, (N - T) // 10):
        d = left_bits(TR[t], t) ^ LR[t]
        if d == 0: out.append((t, None)); continue
        i = d.bit_length() - 1
        out.append((t, round((-(i + 1)) / max(1, t - T), 3)))
    print(w, out)
