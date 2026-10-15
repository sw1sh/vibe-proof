# Control: same driven construction, but period words with some cyclic 1-run of length <= 8.
# If the test harness is sensitive, the conclusion (column -1 P-periodic from T+P+10) should FAIL often.
import random, sys
sys.path.insert(0, "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-C3-longones")
from t3_driven_lib import simulate, cyc_runs

rng = random.Random(7)
res = {}
for L in range(1, 11):
    fails = tot = 0
    for _ in range(60):
        zeros = rng.randint(1, 6)
        w = [0] * zeros + [1] * L          # one 1-run of length exactly L
        if rng.random() < 0.5:             # sometimes add a long run too
            w += [0] * rng.randint(1, 3) + [1] * rng.randint(9, 12)
        P = len(w)
        T = rng.randint(0, 20)
        phase = rng.randrange(P)
        N = T + 9 + P + 1 + 6 * P + 30
        c = [rng.randint(0, 1) for _ in range(T)] + [w[(t - T + phase) % P] for t in range(T, N + 2)]
        # keep the right half random; does column -1 become P-periodic within the window?
        col1, col2, colm1 = simulate(c, N, rng)
        bad = any(colm1[t + P] != colm1[t] for t in range(T + 9 + P + 1, N - P))
        fails += bad; tot += 1
    res[L] = (fails, tot)
    print(f"shortest 1-run L={L:2d}: column -1 NOT P-periodic in {fails}/{tot} trials")
