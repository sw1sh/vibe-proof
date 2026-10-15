#!/usr/bin/env python3
"""Column 1 (both phases) of the true right half at T0 driven by an alternating center: densities by phase."""
import sys
T0, N, ph = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
off = T0 + 2; r = 1 << off
for t in range(T0): r = (r << 1) ^ (r | (r >> 1))
a = (r >> off) & ~1
yw, yb = [], []
for t in range(N):
    c = (t + ph) & 1
    a = (a & ~1) | c
    (yb if c else yw).append((a >> 1) & 1)
    a = ((a << 1) ^ (a | (a >> 1))) & ~1
yw, yb = yw[1000:], yb[1000:]
print(f"col1 at white times: density {sum(yw)/len(yw):.5f}; at black times: {sum(yb)/len(yb):.5f}; overall {(sum(yw)+sum(yb))/(len(yw)+len(yb)):.5f}; 17/56={17/56:.5f}, 3/14={3/14:.5f}")
# column 1 at black times right after a white time: is it determined? print pair stats
