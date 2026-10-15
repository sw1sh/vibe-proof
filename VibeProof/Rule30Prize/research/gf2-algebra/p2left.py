# Hypothesis H: c(t) alternates for t >= T, with c(t)=1 at even t (phase A).
# Derived (valid for t >= T): col_{-1}(2s) = 1, col_{-1}(2s+1) = 1 - b_s, where b_s = col_1(2s+1),
# and the right half forces b to have no two consecutive 1s.
# Leftward recursion: col_{p-1}(t) = col_p(t+1) ^ (col_p(t) | col_{p+1}(t)).
# For random golden-mean b, compute columns -k and report, for each k, which parity classes are constant.
import random, sys
def golden(n, rng, p=0.5):
    b = []; prev = 0
    for _ in range(n):
        x = 0 if prev else (1 if rng.random() < p else 0)
        b.append(x); prev = x
    return b
def run(b, K, phase):
    n = 2 * len(b)
    c = [1 if (t % 2 == phase) else 0 for t in range(n)]
    m1 = [1 if c[t] else 1 - b[t // 2] for t in range(n)]   # col_{-1}: 1 when c(t)=1, else 1 - b
    cols = {0: c, -1: m1}
    for k in range(2, K + 1):
        A = cols[-(k - 1)]; B = cols[-(k - 2)]
        L = len(A) - 1
        cols[-k] = [A[t + 1] ^ (A[t] | B[t]) for t in range(L)]
    return cols
rng = random.Random(5)
K = int(sys.argv[1]) if len(sys.argv) > 1 else 60
for phase in (0, 1):
    stats = {}
    for trial in range(300):
        b = golden(K + 40, rng, rng.choice([0.2, 0.5, 0.8]))
        cols = run(b, K, phase)
        for k in range(1, K + 1):
            col = cols[-k]
            for par in (0, 1):
                vals = set(col[t] for t in range(par, len(col), 2))
                key = (k, par)
                stats[key] = stats.get(key, set()) | vals
    const = [(k, par, list(v)[0]) for (k, par), v in sorted(stats.items()) if len(v) == 1]
    print("phase", phase, "constant parity classes (k, t mod 2, value):", const)
