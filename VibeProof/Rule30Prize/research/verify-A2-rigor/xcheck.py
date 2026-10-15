import sys
RULE = 30
def r30(l, c, r):  # Wolfram code lookup, independent of the xor/or formula
    return (RULE >> (4*l + 2*c + r)) & 1

# 1) ZBL by rule-table lookup: positions p = -K..-1 plus wall p = 0 forced white
def zbl_run(init, T):
    # init: dict depth->bit for depth>=1 ; returns list of rows (depth 0..K)
    K = max(init) + T + 3
    row = [0] + [init.get(k, 0) for k in range(1, K + 1)]
    rows = [row[:]]
    for _ in range(T):
        new = [0] * (K + 1)
        for k in range(1, K):
            # p = -k: left neighbor p-1 = depth k+1, right neighbor p+1 = depth k-1
            new[k] = r30(row[k + 1], row[k], row[k - 1])
        new[0] = 0
        row = new
        rows.append(row[:])
    return rows

# 2) trunc_survives: depth 1 black for t <= n, white at t = n+1
bad = 0
for n in range(1, 80, 2):
    init = {k: 1 for k in range(1, n + 1) if k % 2 == 1}
    rows = zbl_run(init, n + 2)
    ok = all(rows[t][1] == 1 for t in range(n + 1)) and rows[n + 1][1] == 0
    bad += (not ok)
print("trunc_survives failures for odd n<80:", bad)

# 3) off-by-one in prose: n = 2*2^w+3; double step from j = 2^w+1 needs depth1 black at time 2j+2 = n+1
for w in range(0, 5):
    n = 2 * 2**w + 3
    init = {k: 1 for k in range(1, n + 1) if k % 2 == 1}
    rows = zbl_run(init, n + 3)
    j = 2**w + 1
    print(f"w={w} n={n}: depth1 at 2j={2*j}: {rows[2*j][1]}, at 2j+2={2*j+2}: {rows[2*j+2][1]}  (step from G^(2^w+1) survives: {rows[2*j][1]==1 and rows[2*j+2][1]==1})")

# 4) concrete lasso for a wall-window abstraction of width 3 (w=3), plus an edge window of 2 (5 bits)
w = 5
n = 2 * 2**w + 3
init = {k: 1 for k in range(1, n + 1) if k % 2 == 1}
rows = zbl_run(init, 2 * (2**w + 1) + 2)
def alpha(row):
    W = max(k for k in range(len(row)) if row[k] == 1)
    return tuple(row[1:4]) + (row[W], row[W - 1])
seen = {}
for j in range(0, 2**w + 1):
    a = alpha(rows[2 * j])
    if a in seen:
        m, mp = seen[a], j
        surv = all(rows[2*i][1] == 1 and rows[2*i+2][1] == 1 for i in range(mp + 1))
        print(f"lasso: m={m} m'={mp} alpha={a} all steps j<=m' survive: {surv}")
        break
    seen[a] = j

# 5) effective boundary on the true pattern: cell(t+1,-1) = cell(t,-2) xor (cell(t,-1) or (c(t) and c(t+1)))
T = 1500
N = T + 3
row = {0: 1}
cells = []
for t in range(T + 2):
    cells.append(dict(row))
    row = {p: r30(row.get(p - 1, 0), row.get(p, 0), row.get(p + 1, 0)) for p in range(-t - 2, t + 3)}
    row = {p: v for p, v in row.items() if v}
g = lambda t, p: cells[t].get(p, 0)
viol = 0
for t in range(T):
    lhs = g(t + 1, -1)
    rhs = g(t, -2) ^ (g(t, -1) | (g(t, 0) & g(t + 1, 0)))
    viol += (lhs != rhs)
print("effective-boundary violations for t<", T, ":", viol)
