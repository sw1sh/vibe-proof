import sys, numpy as np, itertools
w = sys.argv[1]; K = int(sys.argv[2]); P = len(w); N = 1 << K; mask = N - 1
s = np.arange(N, dtype=np.int64)
succ = np.empty((P, 2, N), dtype=np.int64)
for ph in range(P):
    c = int(w[ph])
    for a in range(2):
        succ[ph, a] = ((((s << 1) | c) ^ (s | (s >> 1) | (a << (K - 1)))) & mask)
col1 = (s & 1).astype(np.int8)
def gfp(pattern):
    X = np.array([col1 == int(pattern[ph]) for ph in range(P)])
    while True:
        Xn = X.copy()
        for ph in range(P):
            nx = (ph + 1) % P
            Xn[ph] &= X[nx][succ[ph, 0]] & X[nx][succ[ph, 1]]
        if (Xn == X).all(): return X
        X = Xn
S = np.zeros((P, N), dtype=bool)
for pat in itertools.product('01', repeat=P):
    S |= gfp(''.join(pat))
Y = S.copy()
while True:
    Yn = Y.copy()
    for ph in range(P):
        nx = (ph + 1) % P
        Yn[ph] |= Y[nx][succ[ph, 0]] & Y[nx][succ[ph, 1]]
    if (Yn == Y).all(): break
    Y = Yn
A = ~Y   # adversary can avoid S forever from these
# within A: how many inputs keep the successor in A?
both = one = 0
forced_bits = {}
for ph in range(P):
    nx = (ph + 1) % P
    k0 = A[nx][succ[ph, 0]]; k1 = A[nx][succ[ph, 1]]
    inA = A[ph]
    both += int((inA & k0 & k1).sum()); one += int((inA & (k0 ^ k1)).sum())
    forced_bits[ph] = (int((inA & k0 & ~k1).sum()), int((inA & k1 & ~k0).sum()))
print(f"w={w} K={K}: avoid-region {int(A.sum())} states; in it, both inputs keep avoiding: {both}, exactly one: {one}")
print("  per phase (forced input 0, forced input 1):", forced_bits)
# column K (the column next to the environment) in A: phase-wise forced values?
for ph in range(P):
    v = (s[A[ph]] >> (K - 1)) & 1
    print(f"  phase {ph}: column K values in avoid region: ones {int(v.sum())} / {len(v)}")
