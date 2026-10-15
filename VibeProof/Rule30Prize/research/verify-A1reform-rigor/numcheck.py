# Independent numerical check of the A1-reformulation claim (ZBL, phase-0 constraint).
# Coordinates: row L : k -> bit for k >= 1 (L[0] = wall = 0).  ZBL step:
#   Z(L)(k) = L(k+1) ^ (L(k) | L(k-1)),  k >= 1,  with L(0) = 0.
import random, itertools, sys

def zstep(L):
    # L: list with L[0]=0, finite length n (cells beyond are 0)
    n = len(L)
    Lx = L + [0, 0]
    out = [0] * (n + 1)
    for k in range(1, n + 1):
        out[k] = Lx[k + 1] ^ (Lx[k] | Lx[k - 1])
    out[0] = 0
    return out

def evolve(L, T):
    rows = [list(L)]
    for _ in range(T):
        rows.append(zstep(rows[-1]))
    return rows

def col(f):
    a = []
    for b in f:
        a += [1, b]
    return a

def theta(f, K):
    # X_0 = 0, X_1 = col(f); X_{k+1}(t) = X_k(t+1) ^ (X_k(t) | X_{k-1}(t)); Theta(k) = X_k(0), k = 0..K
    a = col(f)
    n = len(a)
    prev = [0] * n
    cur = list(a)
    L = [0, cur[0]]
    for k in range(1, K):
        nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)]
        prev, cur = cur[:len(nxt)], nxt
        L.append(cur[0])
    return L  # L[0..K]

random.seed(12345)
ok = True
# (a) forward direction: forward evolution of Theta(f) has column 1 = col(f)
for trial in range(300):
    N = random.randint(1, 40)
    f = [random.getrandbits(1) for _ in range(N)]
    K = 2 * N  # Theta(f)(k) for k <= 2N needs col(f)(0..k-1), available
    L = theta(f, K)
    # x_1(t) depends on L(1..t+1); with L known up to K we can check t <= K-1
    rows = evolve(L, K - 1)
    c1 = [rows[t][1] for t in range(K)]
    if c1 != col(f)[:K]:
        ok = False; print("FAIL (a) forward", f); break
print("(a) forward ok" if ok else "")

# (a) converse / uniqueness: for arbitrary L, the recurrence from column 1 of its evolution reconstructs L
ok2 = True
for trial in range(300):
    K = random.randint(1, 60)
    L = [0] + [random.getrandbits(1) for _ in range(K)]
    rows = evolve(L, K)
    c1 = [rows[t][1] for t in range(K)]
    # spatial recurrence from (0, c1)
    prev = [0] * K; cur = list(c1); rec = [0, cur[0]]
    for k in range(1, K):
        nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)]
        prev, cur = cur[:len(nxt)], nxt
        rec.append(cur[0])
    if rec != L[:K + 1]:
        ok2 = False; print("FAIL (a) converse", L, rec); break
print("(a) converse ok" if ok2 else "")

# (b) triangular form: Theta(f)(2j+1) depends only on f_0..f_{j-1}; Theta(f)(2j) flips with f_{j-1}
# and does not depend on f_j, f_{j+1}, ...
ok3 = True
for trial in range(400):
    N = 24
    f = [random.getrandbits(1) for _ in range(N)]
    K = 2 * N
    L = theta(f, K)
    for i in range(N):
        g = list(f); g[i] ^= 1
        Lg = theta(g, K)
        for k in range(1, K + 1):
            # predicted: Theta(k) depends on f_i only if i <= (k-2)//2 ; k = 2(i+1) flips exactly
            if k == 2 * (i + 1):
                if L[k] == Lg[k]:
                    ok3 = False; print("FAIL pivot", f, i, k)
            elif i > (k - 2) // 2 or k <= 1:
                if L[k] != Lg[k]:
                    ok3 = False; print("FAIL dependence", f, i, k)
        if not ok3: break
    if not ok3: break
print("(b) triangular ok" if ok3 else "")

# (b) equivariance: Z^2 Theta(f) = Theta(sigma f)
ok4 = True
for trial in range(300):
    N = random.randint(3, 40)
    f = [random.getrandbits(1) for _ in range(N)]
    K = 2 * N
    L = theta(f, K)
    Z2 = zstep(zstep(L))  # valid on k where Z2(k) uses L up to k+2 <= K
    Ls = theta(f[1:], K - 2)
    for k in range(1, K - 2 + 1):
        if Z2[k] != Ls[k]:
            ok4 = False; print("FAIL equivariance", f, k); break
    if not ok4: break
print("(b) equivariance ok" if ok4 else "")
print("ALL OK" if (ok and ok2 and ok3 and ok4) else "SOME FAIL")
