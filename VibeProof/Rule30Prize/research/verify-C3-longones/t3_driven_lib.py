# Driven diagrams: column 0 is prescribed (random before T, period word w from T on, random phase),
# columns 1..W at time 0 are random; the right half evolves by rule 30 with column 0 as left input;
# column -1 is then forced by cell_left: cell(t,-1) = c(t+1) xor (c(t) or cell(t,1)).
# Check: (i) key: t >= T+9+P, c(t)=0  =>  cell(t,1) = not c(t-1)
#        (ii) column -1 is P-periodic on [T+9+P+1, N-P)
#        (iii) the hypothesis of C3 holds (sanity: words have cyclic 1-runs >= 9)
import random, sys

def rule(a, b, c): return a ^ (b | c)

def cyc_runs(w):
    if all(w): return None
    k = w.index(0); r = w[k:] + w[:k]
    runs, cur = [], 0
    for x in r + [0]:
        if x: cur += 1
        else:
            if cur: runs.append(cur)
            cur = 0
    return runs

def simulate(c, N, rng):
    W = N + 3
    right = [rng.randint(0, 1) for _ in range(W)]   # columns 1..W at time 0
    col1 = []; col2 = []
    for t in range(N + 1):
        col1.append(right[0]); col2.append(right[1] if len(right) > 1 else None)
        left = [c[t]] + right[:-1]
        right = [rule(left[i], right[i], right[i+1]) for i in range(len(right) - 1)]
    colm1 = [c[t+1] ^ (c[t] | col1[t]) for t in range(N)]
    return col1, col2, colm1

