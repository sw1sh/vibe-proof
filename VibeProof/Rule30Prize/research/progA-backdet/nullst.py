import sys, itertools
exec(open('linrel.py').read().split('# linear span test')[0].replace('m = int(sys.argv[1])', 'm = int(sys.argv[1])'))
def rank_contains(vecs, target):
    piv = {}
    for v in vecs:
        while v:
            p = v.bit_length() - 1
            if p in piv: v ^= piv[p]
            else: piv[p] = v; break
    t = target
    while t:
        p = t.bit_length() - 1
        if p in piv: t ^= piv[p]
        else: return False
    return True
kmax = max(U)
def monomials(deg):
    out = [FULL]
    for d in range(1, deg + 1):
        for c in itertools.combinations(range(m), d):
            v = FULL
            for j in c: v &= V[j]
            out.append(v)
    return out
for K in range(2, 12):
    found = None
    for d in range(0, 4):
        mons = monomials(d)
        vecs = [g & U[k] for k in range(K + 1, kmax + 1) for g in mons]
        if rank_contains(vecs, FULL):
            found = d; break
    # also check common zeros directly
    common = FULL
    for k in range(K + 1, kmax + 1): common &= (U[k] ^ FULL)
    print("K=%d: min Nullstellensatz multiplier degree <= 3: %s ; common zeros of U_k, k in (%d,%d]: %d" % (K, found, K, kmax, bin(common).count('1')))
