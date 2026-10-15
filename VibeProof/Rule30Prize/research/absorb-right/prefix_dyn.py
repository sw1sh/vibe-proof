# Track locked-prefix length d(t) for word w relative to the lock found in a reference run.
import sys, random
sys.path.insert(0, '.')
from lockinfo import lock_table
w = sys.argv[1]; Q = int(sys.argv[2]); seed = int(sys.argv[3]); width = int(sys.argv[4]); steps = int(sys.argv[5])
tab = lock_table(w, 0, 1000, 3, 20000, 40, Q, 6000)
m = 0
while '*' not in tab[m]: m += 1
L = [[int(ch) for ch in tab[j]] for j in range(m)]
random.seed(seed)
row = random.getrandbits(width)
wb = [int(ch) for ch in w]; P = len(wb)
out = []
for t in range(steps):
    # two alignments: lock phase = t mod Q or (t + P) mod Q (when Q = 2P)
    best = 0
    for shift in range(0, Q, P):
        r = (t + shift) % Q
        d = 0
        while d < m and ((row >> d) & 1) == L[d][r]: d += 1
        best = max(best, d)
    out.append(best)
    row = ((row << 1) | wb[t % P]) ^ (row | (row >> 1))
# print compressed: d(t) for t in windows
for t0 in range(0, steps, 100):
    seg = out[t0:t0+100]
    print(f"{t0:5d}: " + ''.join('ABCDEFGHIJKLMNOPQRSTUVWXYZ'[min(x,25)] if x < 26 else '+' for x in seg))
print("m =", m)
