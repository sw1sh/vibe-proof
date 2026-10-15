# Independent Python check: right half driven by (0111)^inf from random finite starts.
# For each trial, find the earliest T from which col1 is Q-periodic up to the horizon, for Q = 4 and 8,
# masked (only times with c(t)=0) and full.
import random, sys
w = sys.argv[1] if len(sys.argv) > 1 else '0111'
steps = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 5)
P = len(w); wb = [int(ch) for ch in w]
def periodic_from(col, Q, masked):
    n = len(col); T = n - Q
    while T > 0 and ((masked and wb[(T - 1) % P] == 1) or col[T - 1] == col[T - 1 + Q]): T -= 1
    return T
out = []
for tr in range(trials):
    W0 = random.choice([16, 100, 200, 1000])
    row = random.getrandbits(W0) | (1 << (W0 - 1))   # bit i <-> position i+1
    col = []
    for t in range(steps):
        col.append(row & 1)
        row = (((row << 1) | wb[t % P]) ^ (row | (row >> 1)))
    out.append((W0, periodic_from(col, P, True), periodic_from(col, P, False), periodic_from(col, 2 * P, False)))
print(w, 'steps', steps)
print('(W0, masked-%d from, full-%d from, full-%d from):' % (P, P, 2 * P))
for o in out: print(o)
