# Independent reimplementation of the adversarial reachable-set certificate (cross-check of reach.c).
# Strip columns 1..W as tuples; driver word w; adversarial input at column W+1.
import sys
W = int(sys.argv[1]); w = sys.argv[2]
p = len(w)
def step(s, c, x):
    # s: tuple of W bits (col1..colW); c: center; x: col W+1
    out = []
    for i in range(W):
        left = c if i == 0 else s[i-1]
        right = x if i == W - 1 else s[i+1]
        out.append(left ^ (s[i] | right))
    return tuple(out)
from itertools import product
R = set(product((0, 1), repeat=W))
hist = {}
t = 0
while True:
    ph = t % p
    key = frozenset(R)
    if ph in hist and hist[ph] == key: break
    hist[ph] = key
    c = int(w[ph])
    R = {step(s, c, x) for s in R for x in (0, 1)}
    t += 1
print('stabilized at', t)
for ph in range(p):
    vals = {s[0] for s in hist[ph]}
    print('phase', ph, 'c =', w[ph], 'col1 values', sorted(vals), 'size', len(hist[ph]))
