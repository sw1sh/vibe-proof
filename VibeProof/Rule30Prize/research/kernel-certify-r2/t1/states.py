import sys
def sxor(g):
    s = g
    for i in range(8): s ^= s >> (1 << i)
    return s
def step(k, A, B, b):
    m = (1 << k) - 1
    s = sxor(A | B)
    return ((s ^ m) | (m + 1)) if b else s
# BFS with dedup, no death (pure prefix tree): count distinct states per depth
Wmax = int(sys.argv[1])
S = {(0, 0)}
for k in range(Wmax):
    T = set()
    for (A, B) in S:
        for b in ([1] if k % 2 == 0 else [0, 1]):
            T.add((B, step(k, A, B, b)))
    S = T
    print(k + 1, len(S), 2 ** ((k + 1) // 2), flush=True)
