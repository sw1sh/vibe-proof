# (1) validate col1_trace against the true rule-30 pattern (single black cell);
# (2) sensitivity: below-threshold r (r < 9) or replacing the black run, periodicity should FAIL
#     for some initial rows, showing the test can detect violations.
import itertools, random, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-bprime-cx')
from driven_check import col1_trace, periodic_from, blocks
from det_check import min_j0

# true rule 30
T = 700
W = 2 * T + 5
off = T + 2
rows = []
row = [0] * W; row[off] = 1
rows.append(row)
for t in range(T):
    new = [0] * W
    for p in range(1, W - 1):
        new[p] = row[p - 1] ^ (row[p] | row[p + 1])
    row = new
    rows.append(row)
center = [rows[t][off] for t in range(T + 1)]
print('center prefix', ''.join(map(str, center[:20])))
# compare: start at time t0, driver = center[t0:], initial row = columns 1..N+1 at time t0
bad = 0
for t0 in [0, 5, 50, 200, 333]:
    N = T - t0
    init = 0
    for i in range(N + 1):
        init |= rows[t0][off + 1 + i] << i
    # col1_trace uses a periodic word; pass the driver as a long 'word' (no wrap within N)
    drv = center[t0:t0 + N] + [0]
    tr = col1_trace(drv, init, N)
    truth = [rows[t0 + s][off + 1] for s in range(N + 1)]
    if tr != truth:
        bad += 1
print('simulator vs true rule 30 mismatches:', bad)

# sensitivity
random.seed(7)
for r in [1, 2, 3, 5, 8]:
    nfail = 0; nruns = 0
    for u in blocks(4):
        word = [1] * r + list(u)
        P = len(word)
        N = 6 * P + 300
        for _ in range(5):
            x = random.getrandbits(N + 1)
            tr = col1_trace(word, x, N)
            ok, _ = periodic_from(tr, P, r)
            nruns += 1
            nfail += (not ok)
    print(f'r={r}: periodicity-from-r failures {nfail}/{nruns}')
# for each u, the smallest r for which every random trial is periodic-from-r (empirical absorption threshold)
random.seed(11)
emp = {}
for u in blocks(7):
    j0 = min_j0(u)
    for r in range(1, 9 * j0 + 1):
        word = [1] * r + list(u)
        P = len(word); N = 6 * P + 200
        allok = True
        for _ in range(8):
            x = random.getrandbits(N + 1)
            ok, _ = periodic_from(col1_trace(word, x, N), P, r)
            if not ok:
                allok = False; break
        if allok:
            emp[''.join(map(str, u))] = (r, max(9, 9 * j0)); break
    else:
        emp[''.join(map(str, u))] = (None, max(9, 9 * j0))
viol = [k for k, (a, b) in emp.items() if a is not None and a > b]
print('blocks where empirical threshold exceeds claimed bound (should be none):', viol)
print('sample empirical thresholds (r_emp, claimed):', list(emp.items())[:12])
