# Python cross-check: zero-phase column-1 determination in the stabilized adversarial reachable set.
import sys
W = int(sys.argv[1]); words = sys.argv[2:]
N = 1 << W; mask = N - 1
def run(w):
    p = len(w)
    def step(s, d, x):
        left = ((s << 1) | d) & mask
        right = (s >> 1) | (x << (W - 1))
        return (left ^ (s | right)) & mask
    R = set(range(N)); hist = {}; t = 0
    while True:
        ph = t % p
        fz = frozenset(R)
        if ph in hist and hist[ph] == fz: break
        hist[ph] = fz
        d = int(w[ph]); R = {step(s, d, x) for s in R for x in (0, 1)}; t += 1
    det = all(len({s & 1 for s in hist[ph]}) == 1 for ph in range(p) if w[ph] == '0')
    return t, det, ''.join(str(next(iter({s & 1 for s in hist[ph]}))) if len({s & 1 for s in hist[ph]}) == 1 else '*' for ph in range(p))
for w in words:
    t, det, pat = run(w)
    print(w, 'stab', t, 'zero-phase col1 determined:', det, 'col1 per phase:', pat)
