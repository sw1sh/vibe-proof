import sys, random
sys.path.insert(0, '.')
from sim import *
w = sys.argv[1]; phase = int(sys.argv[2]); width = int(sys.argv[3]); seed = int(sys.argv[4])
steps = int(sys.argv[5]); ncols = int(sys.argv[6])
random.seed(seed)
row = random.getrandbits(width) if width > 0 else 0
wb = [int(ch) for ch in w]; L = len(wb)
cols = [bytearray(steps) for _ in range(ncols)]
for t in range(steps):
    for j in range(ncols):
        cols[j][t] = (row >> j) & 1
    c = wb[(phase + t) % L]
    row = ((row << 1) | c) ^ (row | (row >> 1))
for j in range(ncols):
    ep = eventual_period(cols[j], maxP=steps // 4)
    print(f"col {j+1}: {ep}")
