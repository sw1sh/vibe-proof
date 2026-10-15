# Independent check: densities h (range r) with sum_i h(G(x)[i..]) = sum_i h(x[i..]) for ALL cyclic x of length N in [Nmin, Nmax]
# (ordinary), and the alternating version on even N.  Solution-space dimension should equal 2^(r-1) (trivial laws).
import sys, numpy as np
def r30_ring(x, N):
    out = 0
    for i in range(N):
        l = (x >> ((i - 1) % N)) & 1; c = (x >> i) & 1; rt = (x >> ((i + 1) % N)) & 1
        out |= (l ^ (c | rt)) << i
    return out
def windows(x, N, r):
    return [sum(((x >> ((i + k) % N)) & 1) << k for k in range(r)) for i in range(N)]
def check(r, Nlist, alt):
    rows = []
    for N in Nlist:
        if alt and N % 2: continue
        for x in range(1 << N):
            y = r30_ring(r30_ring(x, N), N)
            row = np.zeros(1 << r)
            for i, (a, b) in enumerate(zip(windows(y, N, r), windows(x, N, r))):
                s = (-1) ** i if alt else 1
                row[a] += s; row[b] -= s
            rows.append(row)
    M = np.array(rows)
    rk = np.linalg.matrix_rank(M)
    return (1 << r) - rk
for r in range(1, 6):
    print(f'r={r}: ordinary law-space dim = {check(r, range(r + 5, r + 9), False)}, '
          f'alternating law-space dim = {check(r, range(r + 5, r + 11), True)}, trivial = {1 << (r - 1)}')
