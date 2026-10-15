import sys
sys.path.insert(0, '.')
from sim import *
def real_right(W):
    N = W
    row = 1 << N
    for t in range(W):
        row = (row << 1) ^ (row | (row >> 1))
    # now row bit (N + p) <-> position p (since we shift left each step, origin moves): position p at bit N + t + p? 
    return row
# simpler: simulate full row with explicit offset
def real_right2(W):
    off = W + 1
    r = 1 << off
    mask = (1 << (2 * W + 4)) - 1
    for t in range(W):
        r = ((r << 1) ^ (r | (r >> 1))) & mask
    # position p at bit p + off; but note (r<<1) means new[b] = old[b-1] => new[p] gets old[p-1]: correct
    res = 0
    for p in range(1, W + 1):
        if (r >> (p + off)) & 1: res |= 1 << (p - 1)
    return res
W = int(sys.argv[1]); w = sys.argv[2]; ph = int(sys.argv[3]); N = int(sys.argv[4])
row = real_right2(W)
col, _ = run(w, ph, row, N)
h = N // 2
# smallest period of last half
s = col[h:]
n = len(s); f = [-1] * (n + 1); k = -1
for i in range(n):
    while k >= 0 and s[k] != s[i]: k = f[k]
    k += 1; f[i + 1] = k
p = n - f[n]
T = h
while T > 0 and col[T - 1] == col[T - 1 + p]: T -= 1
print(w, ph, "T=", T, "P=", p)
