# Independent check of the ZBL identity's conventions on the true rule-30 pattern.
# cell(t+1,p) = cell(t,p-1) xor (cell(t,p) or cell(t,p+1)); zrow k <-> cell -k.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
OFF = N + 5
W = 2 * N + 11
rows = []
r = [0] * W; r[OFF] = 1; rows.append(r)
for t in range(N):
    p = rows[-1]; q = [0] * W
    for i in range(1, W - 1):
        q[i] = p[i - 1] ^ (p[i] | p[i + 1])
    rows.append(q)
cell = lambda t, x: rows[t][OFF + x]
c = [cell(t, 0) for t in range(N + 1)]
assert c[:20] == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], c[:20]

def zbl(L, steps):  # L[k] for k = 0..len-1, L[0] ignored; returns list of rows
    out = []
    cur = [0] + L[1:] + [0] * (steps + 2)
    out.append(cur[:])
    for _ in range(steps):
        nxt = [0] * len(cur)
        for k in range(1, len(cur) - 1):
            nxt[k] = cur[k + 1] ^ (cur[k] | cur[k - 1])
        cur = nxt; out.append(cur[:])
    return out

agree_ok = 0; neg_control_diff = 0; neg_control_total = 0; bad = 0
# effective boundary identity on the pattern
eb_checked = 0
for t in range(N):
    if not (c[t] and c[t + 1]):
        eb_checked += 1
        assert cell(t + 1, -1) == cell(t, -2) ^ cell(t, -1), t
    if c[t] and not c[t + 1]:
        assert cell(t, -1) == 1, t
for T in range(0, N - 60):
    m = 0
    while T + m < N and not (c[T + m] and c[T + m + 1]):
        m += 1
    m = min(m, N - T - 1)
    L = [cell(T, -k) for k in range(0, T + 2)]
    Z = zbl(L, m + 1)
    for tt in range(0, m + 1):
        for k in range(1, T + tt + 2):
            if Z[tt][k] != cell(T + tt, -k):
                bad += 1
    agree_ok += 1
    # negative control: one step past the run (noBB fails at T+m) there should be a disagreement
    if T + m + 1 <= N:
        neg_control_total += 1
        if any(Z[m + 1][k] != cell(T + m + 1, -k) for k in range(1, T + m + 3)):
            neg_control_diff += 1
print("N", N, "effective-boundary steps checked", eb_checked)
print("windows checked", agree_ok, "mismatches inside noBB windows", bad)
print("negative control: windows where ZBL diverges one step after a BB time:", neg_control_diff, "/", neg_control_total)
