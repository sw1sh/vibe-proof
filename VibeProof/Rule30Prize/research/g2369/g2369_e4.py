import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g2369 import *
sigma = elt('bC')   # b c^-1
tau = elt('aC')     # a c^-1
def depth_profile(w, maxd=12):
    # largest level with a nontrivial section (finitary depth), exploring all vertices
    level = {w}
    for d in range(maxd + 1):
        if all(u == (E,) for u in level):
            return d   # all sections at level d trivial
        nxt = set()
        for u in level:
            for x in (0, 1):
                nxt.add(section(u, x)[1])
        level = nxt
    return None
print('sigma: root', rootperm(sigma), 'sections', section(sigma, 0)[1], section(sigma, 1)[1])
print('tau:   root', rootperm(tau), 'sec0 == sigma', section(tau, 0)[1] == sigma, 'sec1', section(tau, 1)[1])
print('depth sigma, tau:', depth_profile(sigma), depth_profile(tau))
for n in range(0, 6):
    conj = normalize([('c', 1)] * n + list(LET['b']) + list(LET['C']) + [('c', -1)] * n)
    conj2 = normalize([('c', 1)] * n + list(LET['a']) + list(LET['C']) + [('c', -1)] * n)
    print(f'n={n}: depth of c^n sigma c^-n = {depth_profile(conj, 20)}, c^n tau c^-n = {depth_profile(conj2, 20)}')
print('c^-1 sigma c finitary?', depth_profile(normalize([('c', -1)] + list(LET['b']) + list(LET['C']) + [('c', 1)]), 14))
