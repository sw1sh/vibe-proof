# Check eventual periodicity of the one-sided width-K step relations (centre 0 = W, centre 1 = B)
import sys
K = int(sys.argv[1]) if len(sys.argv) > 1 else 8
N = 1 << K
mask = N - 1
def succs(x, c):
    base = (((x << 1) | c) ^ (x | (x >> 1))) & mask
    x_km1 = (x >> (K - 2)) & 1
    z1 = (base & ~(1 << (K - 1))) | ((x_km1 ^ 1) << (K - 1))
    return {base, z1}
def rel(c):
    return [frozenset(succs(x, c)) for x in range(N)]
def compose(A, Bm):  # first A then Bm
    return [frozenset(y for m in A[x] for y in Bm[m]) for x in range(N)]
for c, name in ((0, 'W'), (1, 'B')):
    R1 = rel(c)
    powers = [None, R1]
    for n in range(2, 40):
        powers.append(compose(powers[-1], R1))
    found = None
    for n in range(1, 36):
        if powers[n + 4] == powers[n]:
            found = n; break
    found2 = None
    for n in range(1, 36):
        for per in (1, 2, 3, 4):
            if powers[n + per] == powers[n]:
                found2 = (n, per); break
        if found2: break
    print(f"K={K} {name}: least n with {name}^(n+4)={name}^n: {found}; least (n,period) overall: {found2}")
