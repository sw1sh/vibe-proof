# Independent numerical check of the mechanism behind Theorem D.
# Drive the right half (columns 1..W) of rule 30 by an arbitrary periodic column 0 whose period word
# starts with 1^s 0^r (then an arbitrary block u of length K = P - s - r), from an arbitrary
# right-half state at time 0 (= t1, the start of a black run).  The proof claims that column 1 on
# [e_k, e_k + P) does not depend on k >= 0 (e_k = s + k P), for every right-half state, whenever
# s >= 9 and r >= 1 + 9 * ceil((K + 8) / 2).
import random, sys

def rule(l, c, r):
    return l ^ (c | r)

def run(word, state, steps):
    """column-1 values at times 0..steps; state = columns 1..W at time 0; driver = word^inf."""
    P = len(word)
    row = list(state)
    col1 = [row[0]]
    for t in range(steps):
        drv = word[t % P]
        new = [rule(drv, row[0], row[1])]
        for i in range(1, len(row) - 1):
            new.append(rule(row[i - 1], row[i], row[i + 1]))
        row = new
        col1.append(row[0])
    return col1

def jbound(K):
    return (K + 9) // 2          # = ceil((K + 8) / 2)

rng = random.Random(20261015)
fails = 0
trials = 0
for s in (9, 10, 13):
    for K in (0, 1, 2, 3, 4, 7):
        j = jbound(K)
        r = 1 + 9 * j
        P = s + r + K
        for _ in range(12):
            u = [rng.randint(0, 1) for _ in range(K)]
            word = [1] * s + [0] * r + u
            steps = s + 3 * P
            W = steps + 5
            state = [rng.randint(0, 1) for _ in range(W)]
            col1 = run(word, state, steps)
            ok = all(col1[s + k * P + i] == col1[s + i] for k in (1, 2) for i in range(P))
            trials += 1
            if not ok:
                fails += 1
                print("FAIL", s, r, K, u)
print(f"at the bound: {trials} trials, {fails} failures")

# Informational: below the bound (r = 9 j), is column 1 still forced to repeat?  (not claimed)
below = 0
tot = 0
for s in (9,):
    for K in (0, 3, 7):
        j = jbound(K)
        r = 9 * j - 8
        P = s + r + K
        for _ in range(30):
            u = [rng.randint(0, 1) for _ in range(K)]
            word = [1] * s + [0] * r + u
            steps = s + 3 * P
            state = [rng.randint(0, 1) for _ in range(steps + 5)]
            col1 = run(word, state, steps)
            ok = all(col1[s + k * P + i] == col1[s + i] for k in (1, 2) for i in range(P))
            tot += 1
            below += (not ok)
print(f"below the bound (informational): {tot} trials, {below} where column 1 is not yet repeating from e_0")
