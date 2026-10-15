# Symbolic sideways evolution under the constraint a = 1 f0 1 f1 1 f2 ...
# u_k(s) = C_k(2s), v_k(s) = C_k(2s+1). Represent as functions of window (f_s..f_{s+R-1}) via truth tables
# over R variables: table index i has bit j = f_{s+j}.
import sys
R = int(sys.argv[1]) if len(sys.argv) > 1 else 12
N = 1 << R
FULL = (1 << N) - 1
def var(j):
    # truth table of f_{s+j}
    t = 0
    for i in range(N):
        if (i >> j) & 1: t |= 1 << i
    return t
def shift(tt, depth):
    # (S g)(s) = g(s+1): table over window; requires g depends only on vars 0..R-2
    out = 0
    for i in range(N):
        if (tt >> (i >> 1)) & 1:   # g evaluated at window shifted: vars j -> j+1
            out |= 1 << i
    return out
# careful: shift needs g's table index computed from (f_{s+1},...,f_{s+R-1}, f_{s+R}) -> drop f_s, use i>>1 and top var f_{s+R} unknown -> assume not depended
NOT = lambda a: a ^ FULL
u = {0: 0, 1: FULL}
v = {0: 0, 1: var(0)}
def depends(tt):
    ds = []
    for j in range(R):
        m = 1 << j
        # compare tt with var j flipped
        diff = False
        for i in range(N):
            if ((tt >> i) & 1) != ((tt >> (i ^ m)) & 1): diff = True; break
        if diff: ds.append(j)
    return ds
def anf(tt, nv):
    # Moebius transform over nv vars of table restricted to those vars
    vals = [(tt >> i) & 1 for i in range(1 << nv)]
    a = vals[:]
    for j in range(nv):
        for i in range(1 << nv):
            if i & (1 << j): a[i] ^= a[i ^ (1 << j)]
    terms = []
    for i in range(1 << nv):
        if a[i]:
            terms.append('*'.join('f%d' % j for j in range(nv) if i >> j & 1) or '1')
    return ' + '.join(terms) if terms else '0'
K = int(sys.argv[2]) if len(sys.argv) > 2 else 14
for k in range(1, K):
    u[k + 1] = v[k] ^ (u[k] | u[k - 1])
    v[k + 1] = shift(u[k], 0) ^ (v[k] | v[k - 1])
for k in range(1, K + 1):
    du = depends(u[k]); dv = depends(v[k])
    print(k, 'u deps', du, 'v deps', dv)
    nu = (max(du) + 1) if du else 0
    nv = (max(dv) + 1) if dv else 0
    if nu <= 6: print('   u =', anf(u[k], nu))
    if nv <= 6: print('   v =', anf(v[k], nv))
