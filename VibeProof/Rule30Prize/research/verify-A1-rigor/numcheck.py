"""Independent numeric check of A1 (ZBL realization bijection).
Positions are explicit negative integers; the wall (position 0) is white.
forward(row, T): row = dict pos->bit for pos in -1..-K; rule 30 new(p) = old(p-1) ^ (old(p) | old(p+1)).
"""
import random

def forward_col(row, K, T):
    # row: list r[k-1] = cell at position -k, k = 1..K. Simulate T steps (needs K > T + 1 for exactness).
    cur = {-k: row[k - 1] for k in range(1, K + 1)}
    col = []
    for t in range(T):
        col.append(cur[-1])
        nxt = {}
        for k in range(1, K + 1 - (t + 1)):  # cells still inside the exact light cone
            p = -k
            left = cur.get(p - 1, 0)
            centre = cur[p]
            right = 0 if p + 1 == 0 else cur[p + 1]
            nxt[p] = left ^ (centre | right)
        cur = nxt
    return col

def sideways(a, K):
    # C[k][t] = cell at position -k, time t; C[0] = 0, C[1] = a; C[k+2][t] = C[k+1][t+1] ^ (C[k+1][t] | C[k][t])
    n = len(a)
    C = [[0] * n, list(a)]
    for k in range(0, K - 1):
        m = n - (k + 1)
        C.append([C[k + 1][t + 1] ^ (C[k + 1][t] | C[k][t]) for t in range(m)])
    return [C[k][0] for k in range(1, K + 1)]  # lam a (positions -1..-K)

random.seed(12345)
ok_exist = ok_unique = 0
TRIALS = 300
for trial in range(TRIALS):
    K = 60
    a = [random.getrandbits(1) for _ in range(K + 5)]
    lam = sideways(a, K)
    col = forward_col(lam, K, K // 2)
    ok_exist += (col == a[:K // 2])
    # uniqueness: random row x; its column determines x via the sideways recursion
    x = [random.getrandbits(1) for _ in range(2 * K + 5)]
    colx = forward_col(x, 2 * K + 5, K + 2)
    ok_unique += (sideways(colx, K) == x[:K])
print(f"existence ok {ok_exist}/{TRIALS}; uniqueness ok {ok_unique}/{TRIALS}")
