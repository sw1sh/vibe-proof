# Independent re-implementation (verifier) of the adversarial right-strip certificate.
# Encoding DIFFERENT from reach*.c / reach_py*.py: column j (1..W) lives at bit (W - j),
# i.e. column 1 is the MOST significant bit, column W is bit 0.
# Rule 30 (brief): cell(t+1,p) = cell(t,p-1) xor (cell(t,p) or cell(t,p+1)).
# Strip: column 0 = driver d = w[t mod p]; column W+1 = adversarial x in {0,1}.
import sys
import numpy as np


def successor_tables(W):
    N = 1 << W
    mask = N - 1
    s = np.arange(N, dtype=np.int64)
    tab = {}
    for d in (0, 1):
        left = (s >> 1) | (d << (W - 1))          # left neighbour of column j is column j-1 (one bit higher)
        for x in (0, 1):
            right = ((s << 1) & mask) | x          # right neighbour of column j is column j+1 (one bit lower)
            tab[(d, x)] = (left ^ (s | right)) & mask
    return tab


def selftest(W, tab, trials=2000, seed=1):
    rng = np.random.default_rng(seed)
    for _ in range(trials):
        cols = [int(b) for b in rng.integers(0, 2, W + 2)]  # cols[0]=col0, cols[1..W], cols[W+1]
        new = [cols[j - 1] ^ (cols[j] | cols[j + 1]) for j in range(1, W + 1)]
        enc = 0
        for j in range(1, W + 1):
            enc |= cols[j] << (W - j)
        encn = 0
        for j in range(1, W + 1):
            encn |= new[j - 1] << (W - j)
        assert int(tab[(cols[0], cols[W + 1])][enc]) == encn, "step mismatch"
    return True


def certify(w, W, tab=None, maxit=200000):
    p = len(w)
    N = 1 << W
    if tab is None:
        tab = successor_tables(W)
    R = np.ones(N, dtype=bool)
    hist = [None] * p
    t = 0
    while True:
        ph = t % p
        if hist[ph] is not None and np.array_equal(hist[ph], R):
            break
        hist[ph] = R.copy()
        if t > maxit:
            return None
        d = int(w[ph])
        idx = np.flatnonzero(R)
        S = np.zeros(N, dtype=bool)
        S[tab[(d, 0)][idx]] = True
        S[tab[(d, 1)][idx]] = True
        R = S
        t += 1
    pat = []
    sizes = []
    for ph in range(p):
        idx = np.flatnonzero(hist[ph])
        sizes.append(len(idx))
        vals = set(((idx >> (W - 1)) & 1).tolist())
        pat.append(str(next(iter(vals))) if len(vals) == 1 else '*')
    det = all(pat[ph] != '*' for ph in range(p) if w[ph] == '0')
    return t, det, ''.join(pat), sizes


if __name__ == '__main__':
    W = int(sys.argv[1])
    tab = successor_tables(W)
    selftest(W, tab)
    for w in sys.argv[2:]:
        r = certify(w, W, tab)
        if r is None:
            print(w, 'NO STABILIZATION')
            continue
        t, det, pat, sizes = r
        print(w, 'W=%d' % W, 'stab', t, 'zero-phase col1 determined:', det, 'col1 per phase:', pat, 'min|R|', min(sizes))
