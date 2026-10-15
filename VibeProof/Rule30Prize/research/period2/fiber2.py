# Period-2 fiber: for a finite right half R (cells 1..w at time 0) and trace c(t) = a, 1-a, a, ...,
# reconstruct the unique compatible left half L (cells -1, -2, ... at time 0) by left-permutive inversion.
import random, sys
def forced_left(R, a, K):
    # drive right half with c for K+1 steps; x(t) = cell(t,1)
    c = [(a + t) % 2 for t in range(K + 2)]
    row = 0
    for i, r in enumerate(R): row |= r << i          # bit i <-> p = i+1
    width = len(R) + 1
    x = []
    for t in range(K + 1):
        x.append(row & 1)
        width += 1; mask = (1 << width) - 1
        row = ((((row << 1) | c[t]) & mask) ^ (row | (row >> 1))) & mask
    # left reconstruction: colm[j][t] = cell(t, -j); colm[0] = c; colm[-1] := x at j = -1 handled below
    prev2 = x[:]                       # column +1 (only needed for column -1)
    prev = c[:K + 1]                   # column 0
    L = []
    cur = [c[t + 1] ^ (c[t] | x[t]) for t in range(K)]       # column -1, times 0..K-1
    L.append(cur[0])
    for j in range(2, K + 1):
        nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)]   # column -j
        prev, cur = cur, nxt
        if not cur: break
        L.append(cur[0])
    return L
def check_forward(R, L, a, steps):
    # evolve the full row and verify the center trace alternates
    W = len(L) + len(R) + 2 * steps + 4
    off = len(L) + steps + 2
    row = [0] * W
    for k, v in enumerate(L): row[off - 1 - k] = v
    row[off] = a
    for i, r in enumerate(R): row[off + 1 + i] = r
    for t in range(steps):
        if row[off] != (a + t) % 2: return t
        row = [0] + [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, W - 1)] + [0]
    return None
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
K = 400
for trial in range(8):
    w = random.choice([1, 2, 3, 5, 8, 20])
    R = [random.getrandbits(1) for _ in range(w)]; R[-1] = 1
    a = random.getrandbits(1)
    L = forced_left(R, a, K)
    bad = check_forward(R, L[:K // 3], a, K // 4)
    ones = [k + 1 for k, v in enumerate(L) if v]
    print(f"R={''.join(map(str,R))} a={a}: L[1..60]={''.join(map(str, L[:60]))}  #ones in L[1..{len(L)}]={len(ones)} last one at depth {ones[-1] if ones else None}  forward-check fails at {bad}")
