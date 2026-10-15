import sys, random
sys.path.insert(0, '.')
from sim import *
w = sys.argv[1]; phase = int(sys.argv[2]); width = int(sys.argv[3]); seed = int(sys.argv[4])
steps = int(sys.argv[5]); ncols = int(sys.argv[6]); P = int(sys.argv[7]); tstart = int(sys.argv[8])
random.seed(seed)
row = random.getrandbits(width) if width > 0 else 0
wb = [int(ch) for ch in w]; L = len(wb)
cnt = [[[0,0] for r in range(P)] for j in range(ncols)]
for t in range(steps):
    if t >= tstart:
        for j in range(ncols):
            cnt[j][t % P][(row >> j) & 1] += 1
    c = wb[(phase + t) % L]
    row = ((row << 1) | c) ^ (row | (row >> 1))
print("phase r = t mod P; entries: '0'/'1' if constant, '*' if both occur")
print("col  " + ''.join(str(r % 10) for r in range(P)))
for j in range(ncols):
    s = ''
    for r in range(P):
        a, b = cnt[j][r]
        s += '0' if b == 0 else ('1' if a == 0 else '*')
    print(f"{j+1:3d}  {s}")
