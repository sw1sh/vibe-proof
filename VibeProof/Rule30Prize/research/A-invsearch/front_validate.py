# Cross-check: death time of x0 = S[1..m].v.0^inf by direct simulation vs. front-frame prediction t_a + sigma.
import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import death, stripe, step
K = 56; MASK = (1 << K) - 1
def fstep(W, fodd):
    s1 = 0 if fodd else 1; s2 = 1 if fodd else 0
    return (W ^ (((W << 1) | s1) | ((W << 2) | (s1 << 1) | s2))) & MASK
def predict(m, v):
    L = len(v)
    x = stripe(m) | sum(b << (m + i) for i, b in enumerate(v))
    d = next(k for k in range(m + 1, m + L + 3) if ((x >> (k - 1)) & 1) != (k & 1))
    W = 0
    for i in range(K):
        k = d + i
        if (x >> (k - 1)) & 1: W |= 1 << i
    t = 0
    while t < d - 1:
        W = fstep(W, (d - t) & 1); t += 1
    ta = d - 1
    xx = W
    for s in range(K - 2):
        if (ta + s) % 2 == 0 and not (xx & 1): return ta + s
        xx = ((xx >> 1) ^ (xx | (xx << 1))) & MASK
    return None
random.seed(7); bad = 0
for trial in range(300):
    L = random.randint(1, 7); v = [random.getrandbits(1) for _ in range(L)]
    m = random.randint(0, 1500)
    x = stripe(m) | sum(b << (m + i) for i, b in enumerate(v))
    Dd = death(x, 10 * (m + L) + 200); Dp = predict(m, v)
    if Dd != Dp: bad += 1; print('MISMATCH', m, v, Dd, Dp)
print('front-frame prediction vs direct simulation, 300 random (m, v):', 'all agree' if bad == 0 else f'{bad} mismatches')
