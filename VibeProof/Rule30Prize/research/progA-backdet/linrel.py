# Truth tables of U_k(f) = Lambda(f)(k) over variables f_0..f_{m-1}, as Python ints of 2^m bits.
# Compute Lambda via sideways evolution directly on truth tables: columns C_k(t) for t up to needed.
import sys
m = int(sys.argv[1])
N = 1 << m
FULL = (1 << N) - 1
def var(j):
    # bit i of table = value at assignment i (bit j of i = f_j)
    block = (1 << (1 << j)) - 1  # 2^j ones
    pat = block << (1 << j)       # zeros then ones, period 2^(j+1)
    t = 0
    per = 1 << (j + 1)
    # build by doubling
    t = pat
    length = per
    while length < N:
        t |= t << length
        length <<= 1
    return t & FULL
V = [var(j) for j in range(m)]
# column 1: a(t) = 1 at even t, f_{(t-1)/2} at odd t. Need times 0..T where T ~ 2m+2
Tmax = 2 * m + 2
def a(t):
    if t % 2 == 0: return FULL
    s = (t - 1) // 2
    return V[s] if s < m else None
prev = [0] * (Tmax + 1)            # column 0
cur = [a(t) for t in range(Tmax + 1)]  # column 1
U = {1: cur[0]}
k = 1
while True:
    nxt = []
    for t in range(len(cur) - 1):
        if cur[t + 1] is None or cur[t] is None or prev[t] is None:
            nxt.append(None)
        else:
            nxt.append(cur[t + 1] ^ (cur[t] | prev[t]))
    prev, cur = cur, nxt
    k += 1
    if not cur or cur[0] is None: break
    U[k] = cur[0]
print("computed U_k for k=1..", max(U))
# check against sym.py small cases: U_3 = f0, U_5 = f0
assert U[3] == V[0] and U[5] == V[0]
# linear span test: is FULL in span{U_k : K < k <= kmax}?
def in_span(vecs, target):
    basis = []  # list of (pivot, vec)
    piv = {}
    for v in vecs:
        for p in sorted(piv, reverse=True):
            if (v >> p) & 1: v ^= piv[p]
        if v:
            p = v.bit_length() - 1
            # reduce existing
            piv[p] = v
    t = target
    for p in sorted(piv, reverse=True):
        if (t >> p) & 1: t ^= piv[p]
    return t == 0, len(piv)
kmax = max(U)
for K in range(0, 12):
    ok, rank = in_span([U[k] for k in range(K + 1, kmax + 1)], FULL)
    print("K=%d: 1 in span{U_k: %d<k<=%d}? %s  (rank %d of %d)" % (K, K, kmax, ok, rank, kmax - K))
