# Eventual column-1 language (over-approximation) for driver w: start from the stabilized adversarial reachable set
# at phase 0 (strip width W), then enumerate column-1 words of length L (with adversarial inputs), deduplicating
# (state, word) pairs. Report number of words and the set of words restricted to the zero-phases.
import sys
W = int(sys.argv[1]); w = sys.argv[2]; L = int(sys.argv[3])
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
R0 = hist[0]
print('stabilized at', t, '|R0| =', len(R0))
pairs = {(s, '') for s in R0}
for k in range(L):
    d = int(w[k % p])
    pairs = {(step(s, d, x), word + str(s & 1)) for (s, word) in pairs for x in (0, 1)}
words = sorted({word for (_, word) in pairs})
print('L =', L, 'distinct column-1 words:', len(words))
zp = [ph for ph in range(p) if w[ph] == '0']
zwords = sorted({''.join(wd[i] for i in range(L) if (i % p) in zp) for wd in words})
print('distinct zero-phase subwords:', len(zwords))
for z in zwords[:40]: print(' ', z)
