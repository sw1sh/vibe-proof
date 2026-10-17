import sys, itertools, time; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g2369 import *
t0 = time.time()
NONID = [d for d in DEL if d != E]
# E2: all normal forms with l <= 3 c-letters; report trivial ones with nonzero exponent sum
found = {}
for l in range(1, 4):
    for signs in itertools.product((1, -1), repeat=l):
        for ds in itertools.product(DEL, repeat=l + 1):
            # skip non-normal forms (c^e E c^-e)
            if any(signs[i] == -signs[i + 1] and ds[i + 1] == E for i in range(l - 1)):
                continue
            w = [ds[0]]
            for i in range(l):
                w += [signs[i], ds[i + 1]]
            w = tuple(w)
            if is_trivial(w):
                found.setdefault((l, sum(signs)), []).append(w)
print('trivial normal forms with l<=3:', {k: len(v) for k, v in found.items()}, f'{time.time()-t0:.1f}s')
for k, v in found.items():
    print(k, v[:6])
# E3: c^n d c^-n inside D?  (normalizer / intersections)
for n in range(1, 4):
    hits = []
    for d in NONID:
        for d2 in DEL:
            w = normalize([('c', 1)] * n + [('d', d)] + [('c', -1)] * n + [('d', d2)])
            if is_trivial(w):
                hits.append((d, dinv(d2)))
    print(f'c^{n} d c^-{n} in D:', hits)
# E5: commutation of D with its conjugates c^n D c^-n
for n in range(1, 5):
    comm = []
    for d in NONID:
        for d2 in NONID:
            conj = [('c', 1)] * n + [('d', d2)] + [('c', -1)] * n
            conjinv = [('c', 1)] * n + [('d', dinv(d2))] + [('c', -1)] * n
            w = normalize([('d', d)] + conj + [('d', dinv(d))] + conjinv)
            if is_trivial(w):
                comm.append((d, d2))
    print(f'[d, c^{n} d2 c^-{n}] = 1 for', len(comm), 'of 49 pairs', comm[:10])
print(f'{time.time()-t0:.1f}s')
