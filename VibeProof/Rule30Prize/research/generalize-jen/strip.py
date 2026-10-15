# Adversarial strip model: cols 1..K of the right half, driver c(t) = w[t mod P] at col 0,
# col K+1 chosen freely each step. Iterate reachable sets from ALL states until the per-phase
# sets stabilize; report whether col 1 is constant at each phase (d-forcing) / at zero phases (e-forcing).
import sys, numpy as np

def limit_sets(w, K, maxiter=10000):
    P = len(w); N = 1 << K; mask = N - 1
    s = np.arange(N, dtype=np.int64)
    succ = []
    for ph in range(P):
        c = int(w[ph])
        base = (((s << 1) | c) ^ (s | (s >> 1))) & mask
        succ.append((base, base ^ ((~s >> 0) & 0) | 0))  # placeholder, replaced below
    succ = []
    for ph in range(P):
        c = int(w[ph])
        a0 = ((((s << 1) | c) ^ (s | (s >> 1))) & mask)
        a1 = ((((s << 1) | c) ^ (s | (s >> 1) | (1 << (K - 1)))) & mask)
        succ.append((a0, a1))
    S = [np.ones(N, dtype=bool) for _ in range(P)]
    it = 0
    while True:
        it += 1
        changed = False
        for ph in range(P):
            nx = (ph + 1) % P
            new = np.zeros(N, dtype=bool)
            idx = np.nonzero(S[ph])[0]
            new[succ[ph][0][idx]] = True
            new[succ[ph][1][idx]] = True
            new &= S[nx]          # monotone decreasing iteration
            if new.sum() != S[nx].sum():
                changed = True
            S[nx] = new
        if not changed or it >= maxiter:
            break
    return S, it

def report(w, K):
    S, it = limit_sets(w, K)
    P = len(w)
    col1 = []
    for ph in range(P):
        idx = np.nonzero(S[ph])[0]
        vals = set(np.unique(idx & 1).tolist())
        col1.append(vals)
    dforced = all(len(v) == 1 for v in col1)
    eforced = all(len(col1[ph]) == 1 for ph in range(P) if w[ph] == '0')
    sizes = [int(x.sum()) for x in S]
    return dforced, eforced, col1, sizes, it

if __name__ == '__main__':
    w = sys.argv[1]; K = int(sys.argv[2])
    dforced, eforced, col1, sizes, it = report(w, K)
    print(w, 'K', K, 'iters', it, 'd-forced', dforced, 'e-forced', eforced,
          'col1 per phase', [''.join(str(v) for v in sorted(x)) for x in col1], 'sizes', sizes)
