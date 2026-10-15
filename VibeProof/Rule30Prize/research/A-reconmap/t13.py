# Test self-similarity hypotheses: for transforms T on f, look for positions i,j with L(T f)(i) == L(f)(j) (or complement)
# for all random f; also look for relations L(Tf)(i) == XOR of two L(f) entries.
import sys, random
sys.path.insert(0, '.')
from core import *
random.seed(11)
m = 60
N = 400
samples = [[random.getrandbits(1) for _ in range(2 * m)] for _ in range(N)]
transforms = {
  'even': lambda f: f[0::2],
  'odd': lambda f: f[1::2],
  'double': lambda f: [b for b in f for _ in (0, 1)],
  'ins1': lambda f: [x for b in f for x in (b, 1)],
  'ins0': lambda f: [x for b in f for x in (b, 0)],
  '1ins': lambda f: [x for b in f for x in (1, b)],
  '0ins': lambda f: [x for b in f for x in (0, b)],
  'compl': lambda f: [1 - b for b in f],
  'xorshift': lambda f: [f[i] ^ f[i + 1] for i in range(len(f) - 1)],
  'orshift': lambda f: [f[i] | f[i + 1] for i in range(len(f) - 1)],
}
K = 50
base = [L_of_f(f[:m])[:K] for f in samples]
for name, T in transforms.items():
    tl = [L_of_f(T(f)[:m])[:K] for f in samples]
    # columns as integers over samples
    bc = [sum(base[s][j] << s for s in range(N)) for j in range(K)]
    tc = [sum(tl[s][i] << s for s in range(N)) for i in range(K)]
    ALLs = (1 << N) - 1
    hits = []
    for i in range(K):
        for j in range(K):
            if tc[i] == bc[j]: hits.append((i + 1, j + 1, '='))
            elif tc[i] == bc[j] ^ ALLs: hits.append((i + 1, j + 1, '!'))
    # constant columns
    consts = [(i + 1, 1 if tc[i] == ALLs else 0) for i in range(K) if tc[i] in (0, ALLs)]
    print(name, 'consts:', consts, 'hits:', [h for h in hits if not (h[0] <= 5 and h[1] <= 5)][:20], 'small:', [h for h in hits if h[0] <= 5 and h[1] <= 5][:12])
