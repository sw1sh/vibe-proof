# smallest number k of warm-up periods such that col 1 is constant on R_{kp+phi} for all zero phases phi
import sys, numpy as np
def run(w, W):
    p = len(w); N = 1 << W
    s = np.arange(N, dtype=np.int64)
    cols = [(s >> (i - 1)) & 1 for i in range(1, W + 1)]  # bit i-1 <-> column i (as in reach3; independent of vreach)
    succ = {}
    for d in (0, 1):
        for x in (0, 1):
            r = np.zeros(N, dtype=np.int64)
            for i in range(1, W + 1):
                L = d if i == 1 else cols[i - 2]
                R = x if i == W else cols[i]
                r |= ((L ^ (cols[i - 1] | R)) & 1) << (i - 1)
            succ[(d, x)] = r
    R = np.ones(N, dtype=bool)
    for k in range(0, 200):
        ok = True
        Rp = R.copy()
        for ph in range(p):
            if w[ph] == '0':
                v = (s[Rp] & 1)
                if v.min() != v.max(): ok = False
            d = int(w[ph]); nxt = np.zeros(N, dtype=bool)
            idx = np.nonzero(Rp)[0]
            nxt[succ[(d, 0)][idx]] = True; nxt[succ[(d, 1)][idx]] = True
            Rp = nxt
        if ok: return k
        R = Rp
    return None
for arg in sys.argv[1:]:
    w, W = arg.split(':'); print(w, W, 'min warm-up periods k =', run(w, int(W)))
