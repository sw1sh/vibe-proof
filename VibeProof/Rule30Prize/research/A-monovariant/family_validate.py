# Validate the moving-frame prediction: for u and many n, compare direct ZBL death time with
# (e-1) + Delta(Y(e-1)) computed via the triangular system.
import sys
def zbl_death(L, maxT):
    x = list(L)
    for t in range(maxT + 1):
        if t % 2 == 0 and x[0] == 0: return t
        n = len(x) + 1
        xx = [0] + x + [0, 0]
        x = [xx[k + 1] ^ (xx[k] | xx[k - 1]) for k in range(1, n + 1)]
    return None
s = lambda k: k % 2
def predicted(u, n, J=60):
    r = len(u)
    # first defect e
    c = None
    for i in range(1, r + 1):
        if u[i - 1] != s(n + i): c = i; break
    if c is None:
        i = r + 1
        while s(n + i) == 0: i += 1
        c = i
    e = n + c
    if e % 2 == 1: return e - 1
    Y = [(u[c + j - 1] if c + j <= r else 0) for j in range(J + 1)]
    for t in range(e - 1):
        Y0 = 1 - s(e - t); Y[0] = Y0
        ym1 = s(e - t - 1)
        N = Y[:]
        for j in range(1, J + 1):
            a1 = Y[j - 1]; a2 = Y[j - 2] if j >= 2 else ym1
            N[j] = Y[j] ^ (a1 | a2)
        Y = N
    Y[0] = 1 - s(1)
    cfg = Y[:]   # x_{1+j} = Y_j at the odd time e-1; violation at offsets i odd
    x = cfg[:]
    for i in range(0, J - 2):
        if i % 2 == 1 and x[0] == 0: return (e - 1) + i
        xx = [0] + x + [0, 0]
        x = [xx[k + 1] ^ (xx[k] | xx[k - 1]) for k in range(1, len(x))]
    return None
bad = 0
for u in ([1], [1,1], [0,1], [1,0,1], [1,1,0,1], [0,0,0,1], [1,0,1,1,1,0,1]):
    for n in range(0, 70):
        L = [s(k) for k in range(1, n + 1)] + u
        d1 = zbl_death(L, 400)
        d2 = predicted(u, n)
        if d1 != d2: bad += 1; print("MISMATCH", u, n, d1, d2)
print("mismatches:", bad)
