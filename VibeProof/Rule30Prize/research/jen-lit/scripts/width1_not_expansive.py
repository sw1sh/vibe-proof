# Claim: for every K and 1 <= t <= K there is a finite rule-30 configuration whose column 0 is
# identically 0 on times [0, K] while column -1 is 1 at time t. Compared with the all-zero
# configuration, this shows rule 30 is NOT left expansive with width 1 (Kopra's sense) for any
# rectangle dimensions. Construction: prescribe column 0 = 0 and column 1 = 0^t 1^(K-t+1),
# build columns -1, -2, ... sideways (x[s][p-1] = x[s+1][p] xor (x[s][p] or x[s][p+1])),
# put a single 1 at position t+1 (zeros on [2, t]) on the right, then evolve FORWARD and check.
def rule30(l, c, r): return l ^ (c | r)
def build_row0(K, t):
    col = {0: [0] * (K + 1), 1: [1 if s >= t else 0 for s in range(K + 1)]}
    for p in range(0, -K - 1, -1):           # define column p-1 from columns p, p+1
        n = len(col[p]) - 1
        col[p - 1] = [col[p][s + 1] ^ (col[p][s] | col[p + 1][s]) for s in range(n)]
    row0 = {p: col[p][0] for p in col if len(col[p]) > 0}
    for k in range(2, t + 1): row0[k] = 0
    row0[t + 1] = 1
    return row0
def forward(row0, K):
    lo, hi = min(row0) - K - 2, max(row0) + K + 2
    row = [row0.get(p, 0) for p in range(lo, hi + 1)]
    hist = [row]
    for _ in range(K):
        row = [0] + [rule30(row[i - 1], row[i], row[i + 1]) for i in range(1, len(row) - 1)] + [0]
        hist.append(row)
    return hist, lo
bad = 0
for K in range(1, 41):
    for t in range(1, K + 1):
        hist, lo = forward(build_row0(K, t), K)
        c0 = [hist[s][0 - lo] for s in range(K + 1)]
        cm1 = hist[t][-1 - lo]
        if any(c0) or cm1 != 1: bad += 1
print('violations:', bad, '(checked K <= 40, all 1 <= t <= K)')
fails = []
for K in range(1, 41):
    for t in range(1, K + 1):
        hist, lo = forward(build_row0(K, t), K)
        c0 = [hist[s][0 - lo] for s in range(K + 1)]
        cm1 = hist[t][-1 - lo]
        if any(c0) or cm1 != 1: fails.append((K, t, [s for s in range(K + 1) if c0[s]], cm1))
print(fails[:12])
fails2 = [f for f in fails if f[1] <= f[0] - 1]
print('violations with 1 <= t <= K-1:', len(fails2))
