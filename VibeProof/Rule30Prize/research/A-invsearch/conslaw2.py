# Efficient test: no nontrivial additive conservation law of range r for G = (ECA rule)^iters.
# Densities restricted to H1 = {h supported on r-words ending in 1} (a complement of the trivial laws
# constants + coboundaries).  No nontrivial law  <=>  the map h -> normal form of d(h) is injective on H1
# <=> the 2^(r-1) x (#non-tree edges) matrix has full row rank.  We certify full row rank modulo
# p = 2^31-1 on a random subset of columns (rank_p <= rank_Q, so this certifies rank over Q).
# Option alt=1: alternating (period-2 signed) densities  sum_i (-1)^i k(x[i..i+r)) on even-period configs:
# normalise on the bipartite double cover of the de Bruijn graph.
import sys, numpy as np
P = 2147483647
def eca_vec(rule, w, L):
    # w: numpy int64 array of L-bit words (bit i = cell i). returns image words of length L-2
    out = np.zeros_like(w)
    for i in range(1, L - 1):
        idx = (((w >> (i - 1)) & 1) << 2) | (((w >> i) & 1) << 1) | ((w >> (i + 1)) & 1)
        bit = (rule >> idx) & 1
        out |= bit << (i - 1)
    return out
def rank_mod_p(M):
    M = M.copy() % P
    rows, cols = M.shape
    rk = 0
    for c in range(cols):
        if rk == rows: break
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
def run(rule, iters, r, K, alt, seed=1):
    a = iters; L = r + 2 * a; NW = 1 << L; NV = 1 << (L - 1)
    words = np.arange(NW, dtype=np.int64)
    img = words.copy(); Lc = L
    for _ in range(iters):
        img = eca_vec(rule, img, Lc); Lc -= 2
    mid = (words >> a) & ((1 << r) - 1)
    # rows: u in H1 (cell r-1 = 1)  -> row index (u & ((1<<(r-1))-1))
    H = 1 << (r - 1)
    def Dcol(w, sign, acc):
        # add sign * D[:, w] restricted to H1 rows into acc (dict row->val)
        u = int(img[w])
        if (u >> (r - 1)) & 1: acc[u & (H - 1)] = acc.get(u & (H - 1), 0) + sign
        u = int(mid[w])
        if (u >> (r - 1)) & 1: acc[u & (H - 1)] = acc.get(u & (H - 1), 0) - sign
    rng = np.random.default_rng(seed)
    if not alt:
        # potential g(v) = -sum_{j>=0, v>>j != 0} D[:, v>>j]; normal form d'(w) = D(w) + g(s(w)) - g(t(w)) on non-tree edges
        cand = rng.choice(NV, size=min(K, NV), replace=False)  # non-tree edges: w = NV + c (cell L-1 = 1)
        cols = []
        for c in cand:
            w = NV + int(c)
            acc = {}
            Dcol(w, 1, acc)
            v = w & (NV - 1)
            while v: Dcol(v, -1, acc); v >>= 1          # + g(s(w))
            v = w >> 1
            while v: Dcol(v, 1, acc); v >>= 1           # - g(t(w))
            cols.append(acc)
    else:
        # double cover: vertex (v, q), q in {0,1}; edge (w, q): (s(w), q) -> (t(w), 1-q), weight (-1)^q d(w).
        # Spanning in-tree towards root (0, 0): from (v, q) take edge (v·0, q) to (v>>1, 1-q) until v = 0,
        # then (0, 1) -> (0, 0) via the self-loop edge (0, 1).  Potential: G(v,q) = G(next) - weight(edge).
        # Normal form on any edge e = (w,q): weight(e) + G(s, q) - G(t, 1-q); must vanish on all edges.
        def G(v, q, acc, sign):
            # adds sign * G(v, q) into acc
            while v:
                Dcol(v, -sign * (1 if q == 0 else -1), acc)   # G(v,q) = G(v>>1,1-q) - (-1)^q D(v)
                v >>= 1; q = 1 - q
            if q == 1:
                Dcol(0, -sign * (-1), acc)                    # G(0,1) = G(0,0) - (-1)^1 D(0) ; G(0,0) = 0
        cand = rng.choice(2 * NW, size=min(K, 2 * NW), replace=False)
        cols = []
        for c in cand:
            w = int(c) >> 1; q = int(c) & 1
            acc = {}
            Dcol(w, 1 if q == 0 else -1, acc)
            G(w & (NV - 1), q, acc, 1)
            G(w >> 1, 1 - q, acc, -1)
            cols.append(acc)
    M = np.zeros((H, len(cols)), dtype=np.int64)
    for j, acc in enumerate(cols):
        for i, v in acc.items(): M[i, j] = v
    rk = rank_mod_p(M)
    return rk, H, len(cols)
if __name__ == '__main__':
    rule, iters, r0, r1 = map(int, sys.argv[1:5]); slack = int(sys.argv[5]); alt = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    for r in range(r0, r1 + 1):
        K = (1 << (r - 1)) + slack
        rk, H, nc = run(rule, iters, r, K, alt)
        print(f"rule {rule}^{iters} {'alternating' if alt else 'ordinary'} densities, range r={r}: rank_p={rk} of {H} "
              f"(cols {nc}) -> {'NO nontrivial law' if rk == H else 'undecided/possible law'}")
        sys.stdout.flush()
