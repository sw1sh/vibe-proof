# Finite model: columns 1..K of the right half, driven at column 0 by periodic word w, column K+1 adversarial.
# Check: every run (any start, any adversary) eventually stays in a set where column 1 follows a fixed pattern.
import sys, numpy as np
w = sys.argv[1]; K = int(sys.argv[2]); P = len(w); N = 1 << K; mask = N - 1
s = np.arange(N, dtype=np.int64)
succ = np.empty((P, 2, N), dtype=np.int64)
for ph in range(P):
    c = int(w[ph])
    for a in range(2):
        succ[ph, a] = ((((s << 1) | c) ^ (s | (s >> 1) | (a << (K - 1)))) & mask)
col1 = (s & 1).astype(np.int8)
def gfp(pattern):
    # X[ph] boolean over states: in X iff col1 == pattern[ph] and all successors (both inputs) in X[ph+1]
    X = np.array([col1 == int(pattern[ph]) for ph in range(P)])
    while True:
        Xn = X.copy()
        for ph in range(P):
            nx = (ph + 1) % P
            Xn[ph] &= X[nx][succ[ph, 0]] & X[nx][succ[ph, 1]]
        if (Xn == X).all(): return X
        X = Xn
import itertools
S = np.zeros((P, N), dtype=bool); found = []
for pat in itertools.product('01', repeat=P):
    G = gfp(''.join(pat))
    if G.any(): found.append((''.join(pat), int(G.sum()))); S |= G
Y = S.copy()
while True:
    Yn = Y.copy()
    for ph in range(P):
        nx = (ph + 1) % P
        Yn[ph] |= Y[nx][succ[ph, 0]] & Y[nx][succ[ph, 1]]
    if (Yn == Y).all(): break
    Y = Yn
print(f"w={w} K={K}: closed column-1 patterns {found}; attracted states {int(Y.sum())}/{P*N}; ALL attracted: {bool(Y.all())}")
