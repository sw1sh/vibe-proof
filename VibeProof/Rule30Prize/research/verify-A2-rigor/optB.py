# Check the side remark: optimal B(d) = (max first even death time over supports <= d) - d + 1.
import sys
def zstep(x):            # bit i = index i = position -(i+1); bit 0's right neighbour is the white wall
    return (x >> 1) ^ (x | (x << 1))
def tau(x, cap):         # first even time with column -1 white
    y = x
    for t in range(cap + 1):
        if t % 2 == 0 and (y & 1) == 0:
            return t
        y = zstep(y)
    return None
def lam(a):              # a: list of column -1 values a[0..n); returns lam a on [0, n)
    n = len(a)
    cols = [[False] * (n + 1) for _ in range(n + 2)]
    for t in range(n): cols[1][t] = a[t]
    for k in range(0, n - 1):
        for t in range(0, n - (k + 2) + 1):
            cols[k + 2][t] = cols[k + 1][t + 1] ^ (cols[k + 1][t] or cols[k][t])
    return [cols[i + 1][0] for i in range(n)]
def check_lam_realizes(a):   # sanity: ZBL from lam(a) reproduces column a on [0, n)
    n = len(a); row = lam(a); x = sum(1 << i for i in range(n) if row[i])
    y = x
    for t in range(n):
        # cell (t, idx 0) depends on indices [0, t] of row 0, all within [0, n)
        if bool(y & 1) != a[t]: return False
        y = zstep(y)
    return True
import random
random.seed(1)
for _ in range(300):
    n = random.randint(1, 25); a = [random.random() < 0.5 for _ in range(n)]
    assert check_lam_realizes(a)
def Lmax(d, cap):        # longest white run of lam(alt f) starting at d, over all f (DFS on f prefixes)
    best = 0; stack = [[]]; nodes = 0
    while stack:
        f = stack.pop(); nodes += 1
        k = len(f); n = 2 * k + 1
        a = [True if t % 2 == 0 else f[t // 2] for t in range(n)]
        row = lam(a)
        blk = [i for i in range(d, n) if row[i]]
        if blk:
            best = max(best, blk[0] - d)
        else:
            if n > cap: return None, nodes
            stack.append(f + [False]); stack.append(f + [True])
    return best, nodes
print(" d  tau_max  Lmax  B_opt  tau_max-d+1  Ds=max(tau/2)  Ds-d+1")
for d in range(0, 15):
    cap = 8 * d + 20
    taus = [tau(x, cap) for x in range(1 << d)]
    assert all(t is not None for t in taus), d
    tm = max(taus)
    L, nodes = Lmax(d, cap)
    assert L is not None
    print(f"{d:2d}  {tm:7d}  {L:4d}  {L+1:5d}  {tm-d+1:11d}  {tm//2:13d}  {tm//2-d+1:6d}", flush=True)
    assert L + 1 == tm - d + 1
