import itertools, time
import os; exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'classify_pairs.py')).read().split("JPHI = 13")[0])   # reuse Phi, bdry, canon, cycles
t0 = time.time()
JPHI = 15
MP = 1 << (JPHI + 2)
phi_pairs, comp_pairs = set(), set()
for c in cycles(lambda x: Phi(x) % MP, MP):
    for j in range(0, JPHI + 1):
        seq = tuple(((x >> j) & 1, (x >> (j + 1)) & 1) for x in c)
        phi_pairs.add(canon(seq))
        comp_pairs.add(canon(tuple((1 - a, 1 - b) for a, b in seq)))
print('Phi pairs:', len(phi_pairs), ' complemented:', len(comp_pairs), f'{time.time()-t0:.1f}s')
K = 12
for al, be, ga in [(1, 0, 1), (1, 1, 1)]:
    M = 1 << K
    cs = cycles(lambda x: bdry(al, be, ga, Phi(x)) % M, M)
    real, comp, neither = 0, 0, 0
    for c in cs:
        pairs = [canon(tuple(((x >> k) & 1, (x >> (k + 1)) & 1) for x in c)) for k in range(K - 1)]
        if any(p in phi_pairs for p in pairs): real += len(c)
        elif any(p in comp_pairs for p in pairs): comp += len(c)
        else: neither += len(c)
    print(f'step ({al},{be},{ga}) mod 2^{K}: residues realizable {real}, only via complement {comp}, neither {neither}')
print(f'{time.time()-t0:.1f}s')
