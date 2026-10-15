#!/usr/bin/env python3
"""Independent re-implementation (Python big-int bit vectors) of the period-2 right-half experiment:
right half (columns p >= 1) of single-seed rule 30 at time T0, then driven at column 0 by an alternating
center c(t) = (t + ph) & 1; record y = column 1 at the white center times. Prints gap statistics.
usage: yindep.py T0 N ph [mode]   mode 0: true right half; mode 1: random right half of width T0 (seed T0)."""
import sys, random, collections
T0, N, ph = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
mode = int(sys.argv[4]) if len(sys.argv) > 4 else 0
if mode == 0:
    off = T0 + 2
    r = 1 << off
    for t in range(T0):
        r = (r << 1) ^ (r | (r >> 1))
    a = (r >> off) & ~1           # bit p = cell(T0, p), p >= 1 ; clear column 0
else:
    rnd = random.Random(T0)
    a = sum(rnd.getrandbits(1) << p for p in range(1, T0 + 1))
y = []
for t in range(N):
    c = (t + ph) & 1
    a = (a & ~1) | c
    if c == 0:
        y.append((a >> 1) & 1)
    a = ((a << 1) ^ (a | (a >> 1))) & ~1
y = y[1000:]
pos = [i for i, v in enumerate(y) if v]
gaps = collections.Counter(b - a for a, b in zip(pos, pos[1:]))
n = len(y); ones = sum(y)
print(f"T0={T0} N={N} ph={ph} mode={mode}: samples {n}, density {ones/n:.5f} (3/14={3/14:.5f}), ones-3n/14={ones-3*n/14:.1f}, gaps {sorted(gaps.items())}")
