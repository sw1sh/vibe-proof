# Stress: adversarial prefixes (short 1-runs, 0-runs straddling T), large P and T.
import random, sys
sys.path.insert(0, "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-C3-longones")
from t3_driven_lib import simulate, cyc_runs
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 11)

def random_long_word():
    # alternate 0-runs (length 1..k) and 1-runs (length 9..k), random count
    w = []
    for _ in range(rng.randint(1, 6)):
        w += [0] * rng.randint(1, 25) + [1] * rng.randint(9, 25)
    k = rng.randrange(len(w)); return w[k:] + w[:k]

tot = keyv = perv = 0
latest_key_fail = -10**9
for trial in range(250):
    w = random_long_word()
    assert min(cyc_runs(w)) >= 9
    P = len(w)
    T = rng.randint(0, 120)
    phase = rng.randrange(P)
    # adversarial prefix: short 1-runs separated by single zeros, ending in a 1-run of length < 9
    pre = []
    while len(pre) < T:
        pre += [1] * rng.randint(1, 8) + [0]
    pre = pre[-T:] if T else []
    N = T + 9 + P + 1 + 3 * P + 20
    c = pre + [w[(t - T + phase) % P] for t in range(T, N + 2)]
    col1, col2, colm1 = simulate(c, N, rng)
    kf = [t for t in range(T + 1, N) if c[t] == 0 and col1[t] != 1 - c[t - 1]]
    if kf: latest_key_fail = max(latest_key_fail, max(kf) - (T + 9 + P))
    if any(t >= T + 9 + P for t in kf): keyv += 1
    if any(colm1[t + P] != colm1[t] for t in range(T + 9 + P + 1, N - P)): perv += 1
    tot += 1
print(f"trials={tot} key-violations(t>=T+9+P)={keyv} col-1 periodicity violations={perv}")
print("latest key failure relative to bound T+9+P (negative = before bound):", latest_key_fail)
