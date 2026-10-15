# Scan Lyndon words: smallest strip width K (<= Kmax) at which col 1 is forced at all zero phases (e-forcing)
# and at all phases (d-forcing), in the adversarial-strip limit sets.
import sys, numpy as np, time

def lyndon(n):
    res = []
    for x in range(2**n):
        s = format(x, '0%db' % n)
        if all(s < s[i:] + s[:i] for i in range(1, n)): res.append(s)
    return res

SUCC = {}
def succ_arrays(K):
    if K not in SUCC:
        N = 1 << K; mask = N - 1
        s = np.arange(N, dtype=np.int64)
        d = {}
        for c in (0, 1):
            a0 = ((((s << 1) | c) ^ (s | (s >> 1))) & mask)
            a1 = ((((s << 1) | c) ^ (s | (s >> 1) | (1 << (K - 1)))) & mask)
            d[c] = (a0, a1)
        SUCC[K] = d
    return SUCC[K]

def limit(w, K):
    P = len(w); N = 1 << K
    sc = succ_arrays(K)
    S = [np.ones(N, dtype=bool) for _ in range(P)]
    while True:
        changed = False
        for ph in range(P):
            nx = (ph + 1) % P
            a0, a1 = sc[int(w[ph])]
            new = np.zeros(N, dtype=bool)
            new[a0[S[ph]]] = True
            new[a1[S[ph]]] = True
            new &= S[nx]
            if not changed and not np.array_equal(new, S[nx]): changed = True
            S[nx] = new
        if not changed: break
    vals = []
    for ph in range(P):
        has0 = bool(S[ph][0::2].any()); has1 = bool(S[ph][1::2].any())
        vals.append((has0, has1))
    return vals

if __name__ == '__main__':
    nmin, nmax, Kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    Kmin = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    t0 = time.time()
    for n in range(nmin, nmax + 1):
        for w in lyndon(n):
            Ke = Kd = None
            for K in range(Kmin, Kmax + 1):
                vals = limit(w, K)
                ef = all(not (h0 and h1) for (h0, h1), ch in zip(vals, w) if ch == '0')
                df = all(not (h0 and h1) for (h0, h1) in vals)
                if ef and Ke is None: Ke = K
                if df and Kd is None: Kd = K
                if Ke is not None and Kd is not None: break
                if Ke is not None and K >= Kmax: break
            if Ke is not None or Kd is not None:
                forced = ''.join('-' if (h0 and h1) else ('0' if h0 else '1') for (h0, h1) in limit(w, Ke if Ke else Kd))
                print(f"{w} e-forced K={Ke} d-forced K={Kd} col1/phase={forced}", flush=True)
    print('time', round(time.time() - t0, 1), file=sys.stderr)
