# For the true single-seed rule 30, take the left half at time T as a ZBL start (index i <-> position -(i+1)),
# and compute how long the period-2 constraint survives under the ZBL (phase chosen by column -1 at time 0).
def zstep(x): return (x >> 1) ^ (x | (x << 1))
def full_step(r):  # full row as int with offset
    return (r << 1) ^ (r | (r >> 1))
import sys
Tmax = int(sys.argv[1])
# full rule 30: represent row as int, bit j <-> position j - off
off = Tmax + 2
row = 1 << off
surv = []
for T in range(Tmax + 1):
    # left half at time T: positions -1, -2, ... -> bits off-1, off-2, ...
    x = 0
    for i in range(T + 1):
        if (row >> (off - 1 - i)) & 1: x |= 1 << i
    # survival under ZBL: phase = 0 if x bit0 = 1 else 1 (start one step later)
    y = x; t = 0; phase = 0 if (x & 1) else 1
    while True:
        if t % 2 == phase and not (y & 1): break
        y = zstep(y); t += 1
        if t > 4 * T + 50: t = -1; break
    surv.append(t)
    # advance full rule 30: new(p) = old(p-1) ^ (old(p) | old(p+1)); bit j <-> p = j - off
    # old(p-1) is bit j-1 -> (row << 1); old(p+1) is bit j+1 -> (row >> 1)
    row = (row << 1) ^ (row | (row >> 1))
import collections
print("max survival over T<=%d:" % Tmax, max(surv), " histogram:", sorted(collections.Counter(surv).items())[:20])
