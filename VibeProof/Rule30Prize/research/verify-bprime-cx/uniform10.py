# Side evidence: "1^r 0 uniformly absorbing for r = 14..18". For random right-half starts, is column 1
# eventually P-periodic? Report the latest start of periodicity seen, and any non-periodic cases.
import random, sys, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-bprime-cx')
from driven_check import col1_trace

def periodic_start(tr, P):
    # smallest t0 such that tr[t+P]==tr[t] for all t>=t0 within horizon
    last_bad = -1
    for t in range(len(tr) - P):
        if tr[t + P] != tr[t]:
            last_bad = t
    return last_bad + 1

random.seed(int(sys.argv[1]))
budget = float(sys.argv[2])
t0 = time.time()
for r in range(12, 19):
    word = [1] * r + [0]
    P = r + 1
    N = 3000
    worst = 0; nonper = 0; runs = 0
    tl = time.time()
    while time.time() - tl < budget / 7:
        x = random.getrandbits(N + 1)
        tr = col1_trace(word, x, N)
        s = periodic_start(tr, P)
        runs += 1
        if s > N - 3 * P:
            nonper += 1
        worst = max(worst, s)
    print(f'r={r}: runs={runs}, not periodic by horizon={nonper}, latest periodicity start={worst}', flush=True)
