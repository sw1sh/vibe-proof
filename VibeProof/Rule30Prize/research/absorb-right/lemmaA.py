# Lemma A check: if column m is 1 at times 0..K-1 (driver of the half m+1, m+2, ... is all ones),
# then x(K, m+1) = 0 for every configuration of columns m+1.. at time 0. Brute force over the cone:
# x(K, m+1) depends on x(0, m+1 .. m+1+K). Also report which cells (K, m+i) are forced.
import sys, itertools
K = int(sys.argv[1]); maxi = int(sys.argv[2]) if len(sys.argv) > 2 else 4
# simulate all 2^(K+maxi) initial configs on columns 1..K+maxi (relative), driver 1
W = K + maxi
vals = [set() for _ in range(maxi)]
for X in range(1 << W):
    row = X
    for t in range(K):
        row = (((row << 1) | 1) ^ (row | (row >> 1))) & ((1 << W) - 1)
    # after K steps, cell i (0-based) valid if i + K < W (cone): i < maxi
    for i in range(maxi):
        vals[i].add((row >> i) & 1)
print(f"K={K}: possible values of x(K, m+i) for i=1..{maxi}:", [sorted(v) for v in vals])
