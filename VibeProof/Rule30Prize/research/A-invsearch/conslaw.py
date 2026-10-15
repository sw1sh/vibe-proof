# Additive conservation laws of an elementary CA (or its iterate) with density range r.
# h : {0,1}^r -> Q is conserved by G iff for every spatially periodic x, sum_i h(G(x)[i..i+r)) = sum_i h(x[i..i+r)).
# Equivalently d(w) = h(G(w)) - h(mid(w)) (w of length L = r + 2a, a = radius of G) is a coboundary on the full shift.
# We normalise d along a spanning in-tree of the de Bruijn graph (vertices: (L-1)-words) and require the normal form
# to vanish on all non-tree edges.  Trivial laws (constants + coboundaries of range r) have dimension 2^(r-1).
# Rank is computed exactly modulo the prime p = 2^31 - 1 on a column subset; rank_p <= rank_Q, so if rank_p equals
# 2^r - 2^(r-1) the law space over Q is exactly the trivial one.
import sys, numpy as np
P = 2147483647
def eca(rule, w, L):
    out = 0
    for i in range(1, L - 1):
        l = (w >> (i - 1)) & 1; c = (w >> i) & 1; rt = (w >> (i + 1)) & 1
        # Wolfram code: neighbourhood (left, centre, right) -> bit index 4l+2c+r
        if (rule >> (4 * l + 2 * c + rt)) & 1: out |= 1 << (i - 1)
    return out
def build(rule, iters, r):
    a = iters; L = r + 2 * a
    NW = 1 << L
    img = np.zeros(NW, dtype=np.int64); mid = np.zeros(NW, dtype=np.int64)
    for w in range(NW):
        x = w; Lc = L
        for _ in range(iters):
            x = eca(rule, x, Lc); Lc -= 2
        img[w] = x
        mid[w] = (w >> a) & ((1 << r) - 1)
    R = 1 << r
    D = np.zeros((R, NW), dtype=np.int64)
    D[img, np.arange(NW)] += 1
    D[mid, np.arange(NW)] -= 1
    # potentials on vertices (L-1)-words
    NV = 1 << (L - 1)
    g = np.zeros((R, NV), dtype=np.int64)
    order = sorted(range(1, NV), key=lambda v: v.bit_length())
    for v in order:
        g[:, v] = g[:, v >> 1] - D[:, v]
    nontree = [w for w in range(NW) if (w >> (L - 1)) & 1] + [0]
    nontree = np.array(nontree)
    s = nontree & (NV - 1); t = nontree >> 1
    Dp = D[:, nontree] + g[:, s] - g[:, t]
    return Dp
def rank_mod_p(M):
    M = M.copy() % P
    rows, cols = M.shape
    rk = 0
    for c in range(cols):
        if rk == rows: break
        piv = None
        nz = np.nonzero(M[rk:, c])[0]
        if len(nz) == 0: continue
        piv = rk + nz[0]
        if piv != rk: M[[rk, piv]] = M[[piv, rk]]
        inv = pow(int(M[rk, c]), P - 2, P)
        M[rk] = (M[rk] * inv) % P
        col = M[:, c].copy(); col[rk] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            M[nzr] = (M[nzr] - (col[nzr, None] * M[rk][None, :]) % P) % P
        rk += 1
    return rk
if __name__ == '__main__':
    rule = int(sys.argv[1]); iters = int(sys.argv[2]); r0, r1 = int(sys.argv[3]), int(sys.argv[4])
    ncols = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    rng = np.random.default_rng(1)
    for r in range(r0, r1 + 1):
        Dp = build(rule, iters, r)
        M = Dp
        if ncols and Dp.shape[1] > ncols:
            idx = rng.choice(Dp.shape[1], ncols, replace=False)
            M = Dp[:, idx]
        rk = rank_mod_p(M.T.copy() if M.shape[0] > M.shape[1] else M)
        triv = 1 << (r - 1)
        nlaws = (1 << r) - rk
        print(f"rule {rule}^{iters}, range r={r}: rank_p >= {rk} (cols used {M.shape[1]} of {Dp.shape[1]}), "
              f"law-space dim <= {nlaws}, trivial dim = {triv} -> nontrivial laws: {'NONE' if nlaws == triv else 'possible (' + str(nlaws - triv) + ')'}")
        sys.stdout.flush()
