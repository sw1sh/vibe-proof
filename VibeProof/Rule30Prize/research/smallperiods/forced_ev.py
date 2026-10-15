# Forced left-half cells under the eventual right-half language (adversarial over-approximation).
# Steps: stabilized reachable set at phase 0 (width W), enumerate column-1 words of length L,
# compute a(t) = c(t+1) xor (c(t) | b(t)), left-permutive extension, report forced cells.
import sys
W = int(sys.argv[1]); w = sys.argv[2]; L = int(sys.argv[3]); ncols = int(sys.argv[4])
p = len(w); N = 1 << W; mask = N - 1
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
pairs = {(s, '') for s in hist[0]}
for k in range(L):
    d = int(w[k % p])
    pairs = {(step(s, d, x), word + str(s & 1)) for (s, word) in pairs for x in (0, 1)}
words = sorted({word for (_, word) in pairs})
print('stabilized', t, 'words', len(words))
c = [int(w[i % p]) for i in range(L + 1)]
res = None
for wd in words:
    b = [int(ch) for ch in wd]
    a = [c[i + 1] ^ (c[i] | b[i]) for i in range(L)]
    cols = {0: c[:L], -1: a}
    for n in range(1, ncols):
        xp, xq = cols[-n], cols[-n + 1]
        cols[-n - 1] = [xp[i + 1] ^ (xp[i] | xq[i]) for i in range(len(xp) - 1)]
    if res is None: res = {n: [set() for _ in cols[-n]] for n in range(1, ncols + 1)}
    for n in range(1, ncols + 1):
        for i, v in enumerate(cols[-n]): res[n][i].add(v)
for n in range(1, ncols + 1):
    print('col -%2d: %s' % (n, ''.join(str(next(iter(v))) if len(v) == 1 else '*' for v in res[n])))
