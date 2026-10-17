import sys, itertools, time; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g2369 import *
t0 = time.time()
NAME = {}
for d, w in WORDS.items():
    NAME[d] = ''.join('h' if g == H else 'k' for g in w) or '1'
def show(w):
    s = NAME[w[0]] if w[0] != E else ''
    for i in range(1, len(w), 2):
        s += ('c' if w[i] == 1 else 'C') + (NAME[w[i + 1]] if w[i + 1] != E else '')
    return s
l = 4
counts, examples = {}, {}
for signs in itertools.product((1, -1), repeat=l):
    for ds in itertools.product(DEL, repeat=l + 1):
        if ds[0] != E:   # conjugation: fix d0 = 1 (cyclic words up to the leading D element)
            continue
        if any(signs[i] == -signs[i + 1] and ds[i + 1] == E for i in range(l - 1)):
            continue
        w = [ds[0]]
        for i in range(l):
            w += [signs[i], ds[i + 1]]
        w = tuple(w)
        if is_trivial(w):
            key = sum(signs)
            counts[key] = counts.get(key, 0) + 1
            examples.setdefault(signs, []).append(show(w))
print('trivial l=4 normal forms (d0=1) by exponent sum:', counts, f'{time.time()-t0:.1f}s')
for sg, ex in examples.items():
    print(sg, len(ex), ex[:8])
