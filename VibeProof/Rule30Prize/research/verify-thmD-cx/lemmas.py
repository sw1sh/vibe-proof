"""Adversarial checks of the intermediate lemmas of Theorem D (rule 30, right half).

rule(l, c, r) = l xor (c or r)  (exactly as Rule30Jen.rule).
"""
import itertools, random, sys, time

def rule(l, c, r):
    return l ^ (c | r)

# ---------------------------------------------------------------------------
# 0. sanity: center column from a single black cell matches the brief / A051023
def center_column(n):
    # simulate rows as dict-free lists over p in [-n-1, n+1]
    W = 2 * n + 5
    off = n + 2
    row = [0] * W
    row[off] = 1
    out = [row[off]]
    for t in range(n - 1):
        new = [0] * W
        for p in range(1, W - 1):
            new[p] = rule(row[p - 1], row[p], row[p + 1])
        row = new
        out.append(row[off])
    return out

c = center_column(20)
expect = [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1]
assert c == expect, (c, expect)
print("center column prefix OK:", ''.join(map(str, c)))

# ---------------------------------------------------------------------------
# 1. Lemma A: column m black at times t..t+8 => cells (t+9, m+1), (t+9, m+2) = (0, 1),
#    for every row at time t on columns m+1..m+11 (the full dependency cone).
def run_black(L, k):
    """k steps with black left neighbour; row shrinks by one each step (stepRow)."""
    for _ in range(k):
        L = [rule(1 if i == 0 else L[i - 1], L[i], L[i + 1]) for i in range(len(L) - 1)]
    return L

bad = 0
for bits in itertools.product([0, 1], repeat=11):
    if run_black(list(bits), 9) != [0, 1]:
        bad += 1
print("Lemma A exhaustive over 2^11 rows: failures =", bad)

# Wider row (2^14) to make sure nothing outside the 11-cell cone matters
bad = 0
for bits in itertools.product([0, 1], repeat=14):
    out = run_black(list(bits), 9)
    if out[:2] != [0, 1]:
        bad += 1
print("Lemma A exhaustive over 2^14 wider rows: failures =", bad)

# Tightness: how many black steps are needed in general? (8 should fail)
for k in range(1, 10):
    outs = set(tuple(run_black(list(bits), k)[:2]) for bits in itertools.product([0, 1], repeat=k + 2))
    print(f"  after {k} black steps, possible (col m+1, col m+2): {sorted(outs)}")

# ---------------------------------------------------------------------------
# 2. black_stays: rule(0, 1, x) = 1 ; and the start step rule(0, 0, 1) = 1
assert all(rule(0, 1, x) == 1 for x in (0, 1))
assert rule(0, 0, 1) == 1
print("black_stays truth table OK; rule(0,0,1) = 1 OK")

# ---------------------------------------------------------------------------
# 3. Lemma A*: column m black for 9j steps => columns m+1..m+2j read (01)^j at time t+9j.
#    Exhaustive for j = 1, 2 with bit-sliced big ints; random for j = 3..10.
def bitsliced_check(j):
    n = 11 * j  # dependency cone: columns m+1 .. m+11j at time t
    N = 1 << n
    # cell p (0-based, column m+1+p) as a big int: bit x set iff bit p of x is 1
    def pattern(p):
        block = (1 << (1 << p)) - 1  # 2^p ones
        unit = block << (1 << p)     # zeros then ones, length 2^(p+1)
        reps = N >> (p + 1)
        # replicate unit reps times
        res = 0
        width = 1 << (p + 1)
        # doubling replication
        acc, accw, cnt = unit, width, 1
        out, outw = 0, 0
        r = reps
        while r:
            if r & 1:
                out |= acc << outw
                outw += accw
            acc |= acc << accw
            accw *= 2
            r >>= 1
        return out
    ALL = (1 << N) - 1
    row = [pattern(p) for p in range(n)]
    left = ALL  # column m black
    for step in range(9 * j):
        new = []
        for i in range(len(row) - 1):
            l = left if i == 0 else row[i - 1]
            new.append(l ^ (row[i] | row[i + 1]))
        row = new
    assert len(row) == 2 * j
    fails = 0
    for i in range(2 * j):
        want = ALL if i % 2 == 1 else 0
        if row[i] != want:
            fails += 1
    return fails

for j in (1, 2):
    t0 = time.time()
    print(f"Lemma A* exhaustive j={j} (2^{11*j} rows): failing columns =", bitsliced_check(j),
          f"({time.time()-t0:.1f}s)")

random.seed(12345)
for j in range(3, 11):
    fails = 0
    trials = 3000 if j <= 6 else 1000
    for _ in range(trials):
        L = [random.getrandbits(1) for _ in range(11 * j + 3)]
        out = run_black(L, 9 * j)
        if out[:2 * j] != [0, 1] * j:
            fails += 1
    print(f"Lemma A* random j={j}: {trials} rows, failures = {fails}")

# adversarial rows for Lemma A*: all 0, all 1, alternating, period-3 patterns
for j in range(1, 9):
    for name, gen in [("zeros", lambda i: 0), ("ones", lambda i: 1), ("01", lambda i: i % 2),
                      ("10", lambda i: 1 - i % 2), ("001", lambda i: int(i % 3 == 2)),
                      ("110", lambda i: int(i % 3 != 2))]:
        L = [gen(i) for i in range(11 * j + 3)]
        out = run_black(L, 9 * j)
        if out[:2 * j] != [0, 1] * j:
            print("  Lemma A* FAILS for", name, j)
print("Lemma A* adversarial rows done")
