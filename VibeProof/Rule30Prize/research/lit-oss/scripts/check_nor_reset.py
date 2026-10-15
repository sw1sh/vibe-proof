# Independent check of foundry's alternating-centre right-boundary claims.
# Right half cells x[1..W]; centre prescribed: 0 at even t, 1 at odd t.
# Cells beyond W are free (we enumerate all of them up to width W, and only
# trust outputs whose dependency cone lies inside the window).
import itertools, sys
def step_right(cells, c):
    # cells: list, index 0 -> position 1. returns new list, shorter by 1 (lost rightmost dependence)
    n = len(cells)
    new = []
    for j in range(n - 1):
        left = c if j == 0 else cells[j-1]
        new.append(left ^ (cells[j] | cells[j+1]))
    return new
def outputs(cells, returns):
    # s_k = x_1 at time 2k, k = 0..returns
    s = [cells[0]]
    cur = cells
    for k in range(returns):
        cur = step_right(cur, 0)
        cur = step_right(cur, 1)
        s.append(cur[0])
    return s
# 1) NOR reset identity on all 3-cell (+ free) windows
ok = True
for bits in itertools.product([0,1], repeat=5):
    s,u,v = bits[0],bits[1],bits[2]
    out = outputs(list(bits), 1)
    if out[1] != (1-s)*(1-u)*(1-v): ok = False
print("NOR reset identity:", ok)
# 2) language of s words of length L from all right windows wide enough
for L in range(2, 9):
    W = 2*(L-1) + 2   # cone width needed for s_{L-1}: 2(L-1)+1 cells, +1 margin
    words = set()
    for bits in itertools.product([0,1], repeat=W):
        words.add(tuple(outputs(list(bits), L-1)))
    has11 = any(any(w[i]==1 and w[i+1]==1 for i in range(L-1)) for w in words)
    has00000 = any(any(all(w[i+j]==0 for j in range(5)) for i in range(L-4)) for w in words) if L>=5 else False
    print(f"L={L} W={W} #words={len(words)} contains11={has11} contains00000={has00000}")
