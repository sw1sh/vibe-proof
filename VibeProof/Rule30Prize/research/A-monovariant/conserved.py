# Additive conserved quantities of rule 30 (and rule 30^2) on finite configurations of Z.
# phi: {0,1}^r -> Q, phi(0^r)=0.  Conserved: sum_k phi(F(x)[k..k+r-1]) = sum_k phi(x[k..k+r-1]) for all finite x.
# Trivial: coboundaries phi(p) = h(p[1:]) - h(p[:-1]) (dimension 2^(r-1)-1). Rank computed mod a large prime.
import sys, itertools
P = 2**61 - 1
def r30(x):  # x: tuple, finite support, padded; returns F(x) with length+2 (k-coords x_k' = x_{k+1} ^ (x_k | x_{k-1}))
    n = len(x)
    xx = (0, 0) + x + (0, 0)
    return tuple(xx[i + 1] ^ (xx[i] | xx[i - 1]) for i in range(1, n + 3))
def counts(x, r):
    xx = (0,) * (r - 1) + x + (0,) * (r - 1)
    c = {}
    for k in range(len(xx) - r + 1):
        p = xx[k:k + r]
        if any(p): c[p] = c.get(p, 0) + 1
    return c
def rank_mod(rows, ncols):
    rows = [r[:] for r in rows]
    rank = 0; col = 0
    piv_rows = []
    m = len(rows)
    for col in range(ncols):
        pr = None
        for i in range(rank, m):
            if rows[i][col] % P: pr = i; break
        if pr is None: continue
        rows[rank], rows[pr] = rows[pr], rows[rank]
        inv = pow(rows[rank][col], P - 2, P)
        rows[rank] = [(v * inv) % P for v in rows[rank]]
        for i in range(m):
            if i != rank and rows[i][col] % P:
                f = rows[i][col]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank
def analyze(r, steps, L):
    pats = [p for p in itertools.product((0, 1), repeat=r) if any(p)]
    idx = {p: i for i, p in enumerate(pats)}
    rows = []
    for n in range(1, L + 1):
        for x in itertools.product((0, 1), repeat=n):
            if x[0] == 0 or x[-1] == 0: continue
            y = x
            for _ in range(steps): y = r30(y)
            c1, c0 = counts(y, r), counts(x, r)
            row = [0] * len(pats)
            for p, v in c1.items(): row[idx[p]] += v
            for p, v in c0.items(): row[idx[p]] -= v
            if any(row): rows.append([v % P for v in row])
    rk = rank_mod(rows, len(pats))
    nsol = len(pats) - rk
    triv = 2 ** (r - 1) - 1
    return len(pats), rk, nsol, triv
for steps in (1, 2):
    for r in range(1, int(sys.argv[1]) + 1):
        npat, rk, nsol, triv = analyze(r, steps, int(sys.argv[2]))
        print(f"rule30^{steps}, range r={r}: unknowns {npat}, rank {rk}, solution dim {nsol}, trivial (coboundary) dim {triv}  -> nontrivial: {nsol - triv}")
