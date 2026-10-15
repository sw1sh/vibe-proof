# Which sequences z_k = col1(T+2k+1) can a right half (columns 1..K, column K+1 free each step)
# produce when driven by c = (10)^inf (c(T+2k)=1, c(T+2k+1)=0)?  Count realizable words of length n
# (as subsets reachable from ANY initial state), compare with the golden-mean count (no "11").
import sys, itertools
K = int(sys.argv[1]); n = int(sys.argv[2])
N = 1 << K
def step(s, c, a):
    # s: bits 0..K-1 = columns 1..K; new col_i = col_{i-1} ^ (col_i | col_{i+1}); col_0 = c, col_{K+1} = a
    out = 0
    for i in range(K):
        l = c if i == 0 else (s >> (i-1)) & 1
        m = (s >> i) & 1
        r = a if i == K-1 else (s >> (i+1)) & 1
        out |= (l ^ (m | r)) << i
    return out
# two-step transition from even-time state: even (c=1) then odd (c=0); output col1 at the odd time
succ = [[] for _ in range(N)]
for s in range(N):
    for a1 in (0, 1):
        s1 = step(s, 1, a1)            # state at odd time
        z = s1 & 1
        for a2 in (0, 1):
            s2 = step(s1, 0, a2)       # state at next even time
            succ[s].append((z, s2))
# set of states compatible with an output word: forward subset construction from all states
from collections import Counter
cur = {(): set(range(N))}
for L in range(n):
    nxt = {}
    for word, S in cur.items():
        for z in (0, 1):
            T = set()
            for s in S:
                for (zz, s2) in succ[s]:
                    if zz == z: T.add(s2)
            if T: nxt[word + (z,)] = T
    cur = nxt
words = list(cur.keys())
gm = [w for w in itertools.product((0,1), repeat=n) if all(not (w[i] and w[i+1]) for i in range(n-1))]
print(f"K={K} n={n}: realizable z-words {len(words)}, golden-mean words {len(gm)}, all realizable are golden-mean: {set(words) <= set(gm)}")
