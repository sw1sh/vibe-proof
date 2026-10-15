# Numerical cross-check of Theorem B' (independent of the proof): drive the right half
# (columns >= 1) by column 0 = (1^r u)^infinity starting at time 0, from random initial
# right-half states. The theorem's proof says column 1 is then P-periodic from time r,
# P = r + |u|, whatever the initial state, whenever r >= max(9, 9 j0(u)).
import random, sys

def rule(l, c, r):
    return l ^ (c | r)

def col1(drv, init):
    """drv: column-0 values at times 0..n-1; init: columns 1..len(init) at time 0 with
    len(init) >= n + 1. Returns column-1 values at times 0..n."""
    cur = list(init)
    out = [cur[0]]
    for d in drv:
        cur = [rule(d if i == 0 else cur[i - 1], cur[i], cur[i + 1]) for i in range(len(cur) - 1)]
        out.append(cur[0])
    return out

table = {}
for line in open(sys.argv[1]):
    line = line.strip()
    if line:
        w, j = line.split(':')
        table[tuple(int(c) for c in w.strip())] = int(j)

rng = random.Random(12345)
bad = 0
checked = 0
smaller_fail = 0
for u, j0 in sorted(table.items(), key=lambda x: (len(x[0]), x[0])):
    for r in sorted({max(9, 9 * j0), max(9, 9 * j0) + 1, 36}):
        P = r + len(u)
        word = [1] * r + list(u)
        n = r + 6 * P
        drv = [word[t % P] for t in range(n)]
        for trial in range(20):
            init = [rng.randint(0, 1) for _ in range(n + 1)]
            c1 = col1(drv, init)
            ok = all(c1[t + P] == c1[t] for t in range(r, n + 1 - P))
            checked += 1
            if not ok:
                bad += 1
                print("VIOLATION", u, r, trial)
    # informational: r one step below the bound (if still >= 9)
    r = 9 * j0 - 1
    if r >= 9:
        P = r + len(u)
        word = [1] * r + list(u)
        n = r + 6 * P
        drv = [word[t % P] for t in range(n)]
        for trial in range(20):
            init = [rng.randint(0, 1) for _ in range(n + 1)]
            c1 = col1(drv, init)
            if not all(c1[t + P] == c1[t] for t in range(r, n + 1 - P)):
                smaller_fail += 1
                break
print(f"runs checked: {checked}, violations: {bad}")
print(f"blocks where r = 9*j0-1 already breaks P-periodicity from time r (some trial): {smaller_fail}")
