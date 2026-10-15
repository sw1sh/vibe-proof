# Model of the anti-diagonal DFS for Q01 (ZBL), cross-checked against direct recon.
import sys, random
from functools import lru_cache

def recon_direct(y, k, t):
    # recon y 0 t = False; recon y 1 t = y[t]; recon y (k+2) t = recon y (k+1) (t+1) xor (recon y (k+1) t or recon y k t)
    @lru_cache(None)
    def r(k, t):
        if k == 0: return 0
        if k == 1: return y[t]
        return r(k-1, t+1) ^ (r(k-1, t) | r(k-2, t))
    return r(k, t)

def sxor(g, rounds=8):
    s = g
    for i in range(rounds):
        s ^= s >> (1 << i)
    return s

def step(k, A, B, b):
    m = (1 << k) - 1
    g = (A | B) & m
    s = sxor(g) & m
    if b: s ^= m
    return s | ((1 << k) if b else 0)

# check rep: D_k bit j = recon y (k-j) j
random.seed(1)
for trial in range(200):
    n = 60
    y = [random.randint(0,1) for _ in range(2*n)]
    A, B = 0, 0  # D_{-1} (irrelevant), D_0
    for k in range(n):
        C = step(k, A, B, y[k])
        for j in range(n+2):
            want = recon_direct(tuple(y), k+1-j, j) if j <= k+1 else 0
            if ((C >> j) & 1) != want:
                print("MISMATCH", trial, k, j); sys.exit(1)
        A, B = B, C
print("step model OK")

def count(W, maxdepth=400):
    # DFS without dedup: returns (nodes, deepest surviving depth)
    nodes = 0; deepest = 0
    stack = [(0, 0, 0)]
    while stack:
        k, A, B = stack.pop()
        if k >= maxdepth: raise Exception("maxdepth")
        for b in ([1] if k % 2 == 0 else [0, 1]):
            C = step(k, A, B, b); nodes += 1
            if k + 1 > W and (C & 1): continue
            deepest = max(deepest, k + 1)
            stack.append((k + 1, B, C))
    return nodes, deepest

for W in range(1, int(sys.argv[1]) + 1):
    nodes, deepest = count(W)
    print(W, nodes, deepest, flush=True)
