import numpy as np
from math import comb
rng = np.random.default_rng(1)
# identities mod 2: Lucas product, hockey stick, Pascal
for t in range(300):
    for m in range(70):
        assert (comb(t, m) & 1) == int((t & m) == m)
        for m2 in range(0, 70, 7):
            assert ((comb(t, m) * comb(t, m2)) & 1) == (comb(t, m | m2) & 1)
        assert sum(comb(s, m) for s in range(t)) == comb(t, m + 1)
        if m >= 1:
            assert (comb(t + 1, m) + comb(t, m)) % 2 == comb(t, m - 1) % 2
def mahler(u):
    a = u.copy(); h = 1
    while h < len(a):
        b = a.reshape(-1, 2, h); b[:, 1, :] ^= b[:, 0, :]; h *= 2
    return a
def top(u):
    nz = np.nonzero(mahler(u))[0]; return -1 if len(nz) == 0 else int(nz[-1])
def from_mu(mu, n):
    t = np.arange(n); out = np.zeros(n, dtype=np.uint8)
    for m in np.nonzero(mu)[0]: out ^= ((t & m) == m).astype(np.uint8)
    return out
cnt = 0
for trial in range(3000):
    k = int(rng.integers(1, 9)); M = 1 << k; n = 2 * M
    muA = np.zeros(n, dtype=np.uint8); muA[:M] = rng.integers(0, 2, M); muA[M] = 1
    ms = int(rng.integers(0, M))
    muB = np.zeros(n, dtype=np.uint8); muB[:ms] = rng.integers(0, 2, ms); muB[ms] = 1
    A = from_mu(muA, n); B = from_mu(muB, n)
    assert top(A) == M and top(B) == ms
    tOR = top(A | B)
    if ms >= 1:
        assert tOR == M + ms, (k, ms, tOR); cnt += 1
    else:
        assert tOR == 0  # B == 1 -> A or B == 1: hypothesis L_{j-1}>=2 is needed
print("identities OK; random lemma (d) instances:", cnt)
