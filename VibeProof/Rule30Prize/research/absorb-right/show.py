import sys, random
sys.path.insert(0, '.')
from sim import *
w = sys.argv[1]; phase = int(sys.argv[2]); width = int(sys.argv[3]); seed = int(sys.argv[4])
t0 = int(sys.argv[5]); t1 = int(sys.argv[6]); ncols = int(sys.argv[7])
random.seed(seed)
row = random.getrandbits(width) if width > 0 else 0
wb = [int(ch) for ch in w]; L = len(wb)
for t in range(t1):
    if t >= t0:
        c = wb[(phase + t) % L]
        s = ''.join('#' if (row >> i) & 1 else '.' for i in range(ncols))
        print(f"{t:6d} {(phase+t)%L} {'#' if c else '.'}|{s}")
    c = wb[(phase + t) % L]
    row = ((row << 1) | c) ^ (row | (row >> 1))
