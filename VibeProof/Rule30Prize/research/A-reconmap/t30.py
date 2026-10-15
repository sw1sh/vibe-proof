# Random large-K check of stripe absorption (odd phase), and the even phase S' (black at even k).
import sys, random
sys.path.insert(0, '.')
def run(inner, K, phase, maxT):
    # cells 1..K-1 = inner; cells >= K follow stripe phase: phase 1 -> black at odd k, phase 0 -> black at even k
    n = K - 1
    # simulate on [1, K + maxT + 2] with stripe tail (the far end only matters after maxT steps)
    Ltot = K + maxT + 4
    row = list(inner) + [1 if (k % 2 == phase) else 0 for k in range(K, Ltot + 1)]
    ys = []
    for t in range(maxT):
        ys.append(row[0])
        ext = [0] + row + [row[-2]]   # far end: continue stripe (row[-2] has the right parity)
        row = [ext[k + 1] ^ (ext[k] | ext[k - 1]) for k in range(1, len(row) + 1)]
    return row, ys
random.seed(9)
for phase in (1, 0):
    worst = 0
    for trial in range(60):
        K = random.choice([101, 151, 201]) + (0 if phase == 1 else 1)
        inner = [random.getrandbits(1) for _ in range(K - 1)]
        maxT = 6 * K
        row, ys = run(inner, K, phase, maxT)
        # last time y deviates from its eventual pattern
        if phase == 1:
            last_bad = max([t for t, y in enumerate(ys) if y != 1], default=-1)
        else:
            # A/B cycle: y alternates 1,0 ; find the last t where y_t == y_{t+1}... measure last time pattern not alternating
            last_bad = max([t for t in range(len(ys) - 1) if ys[t] == ys[t + 1]], default=-1)
        ok_final = all(row[k - 1] == (k % 2 == phase) for k in range(2, K + 10))
        worst = max(worst, last_bad / K)
        if not ok_final: print('phase', phase, 'K', K, 'did not converge within', maxT)
    print('phase %d: worst (last deviating time)/K = %.3f' % (phase, worst))
