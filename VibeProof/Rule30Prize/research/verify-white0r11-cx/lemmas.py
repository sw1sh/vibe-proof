# Adversarial checks of the intermediate lemmas of the 0^r 11 absorption proof.
import random, itertools, sys

def rule(a, b, c): return a ^ (b | c)

# ---------- true rule 30 pattern, sanity ----------
def true_rows(T):
    W = T + 2
    row = {0: 1}
    rows = []
    for t in range(T + 1):
        rows.append(dict(row))
        new = {}
        for p in range(-t - 1, t + 2):
            v = rule(row.get(p - 1, 0), row.get(p, 0), row.get(p + 1, 0))
            if v: new[p] = 1
        row = new
    return rows
rows = true_rows(40)
c = [r.get(0, 0) for r in rows]
assert c[:20] == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], c[:20]
assert all(rows[t].get(t, 0) == 1 for t in range(41))
assert all(all(v == 0 or p <= t for p, v in rows[t].items()) for t in range(41))
print("true pattern sanity ok")

# ---------- Lemma A by brute force ----------
def run_black(L, k):
    for _ in range(k):
        L = [rule(1 if i == 0 else L[i - 1], L[i], L[i + 1]) for i in range(len(L) - 1)]
    return L
bad = [L for L in itertools.product([0, 1], repeat=11) if run_black(list(L), 9) != [0, 1]]
print("Lemma A (9 black) counterexamples:", len(bad))
# is 9 sharp? with 8 black steps, what can (m+1) be?
vals8 = set(tuple(run_black(list(L), 8)) for L in itertools.product([0, 1], repeat=10))
print("after 8 black steps, possible (col m+1, col m+2):", sorted(vals8))

# ---------- driven right half ----------
def step_right(row, d):
    # row: list of columns 1..W (index 0 = column 1); d = column 0 value at this time
    # returns next row of same width (rightmost cell uses 0 beyond W -> only valid if config finite)
    W = len(row)
    ext = row + [0, 0]
    return [rule(d if p == 0 else ext[p - 1], ext[p], ext[p + 1]) for p in range(W)]

def first_black(row):
    for i, v in enumerate(row):
        if v: return i  # ell = i (first black at column i+1)
    return None

random.seed(12345)
fails = []
ntests = 0
for trial in range(40000):
    r = random.randint(1, 30)
    # choose ell, sometimes near the thresholds
    choice = random.random()
    if choice < 0.5:
        ell = random.choice([0, 1, 2, max(0, r - 9), max(0, r - 8), max(0, r - 7), r - 1 if r >= 1 else 0, r, r + 1, r + 2, r + 3, r + 4, r + 5, r + 9])
    else:
        ell = random.randint(0, 2 * r + 10)
    W = ell + 1 + r + 60
    row = [0] * ell + [1] + [random.randint(0, 1) for _ in range(W - ell - 1)]
    # make finite: zeros beyond some random point, with plenty of zero margin
    cut = random.randint(ell + 1, W - 1)
    row = row[:cut] + [0] * (W - cut) + [0] * (r + 10)
    # driver: 0^r 1 1 then random
    drv = [0] * r + [1, 1] + [random.randint(0, 1) for _ in range(5)]
    hist = [row]
    for t in range(r + 3):
        hist.append(step_right(hist[-1], drv[t]))
    col = lambda t, p: hist[t][p - 1]
    ntests += 1
    # front_moves
    for i in range(0, min(r, ell) + 1):
        ok = all(col(i, p) == 0 for p in range(1, ell - i + 1)) and col(i, ell - i + 1) == 1
        if not ok: fails.append(("front_moves", r, ell, i)); break
    # black_stays (whenever column 1 is black at some time a+i during the white run, it stays black through a+r)
    for i in range(0, r + 1):
        if col(i, 1) == 1:
            if not all(col(j, 1) == 1 for j in range(i, r + 1)):
                fails.append(("black_stays", r, ell, i))
            break
    if ell <= r - 8 and r >= 8:
        ok = all(col(i, 1) == 1 for i in range(ell, r + 1)) and col(r + 1, 1) == 0 and col(r + 2, 1) == 1
        if not ok: fails.append(("period_lock", r, ell))
    if ell <= r:
        ok = col(r + 2, 1) == 1 or (col(r + 2, 1) == 0 and col(r + 2, 2) == 1)
        if not ok: fails.append(("period_late", r, ell))
    z = ell - r
    if z == 1:
        if not (col(r + 2, 1) == 0 and col(r + 2, 2) == 1): fails.append(("z1", r, ell))
    if z == 2:
        if not (all(col(i, 1) == 0 for i in range(0, r + 1)) and col(r + 1, 1) == 1): fails.append(("z2", r, ell))
    if z == 3:
        if not (col(r + 2, 1) == 0 and col(r + 2, 2) == 0 and col(r + 2, 3) == 1): fails.append(("z3", r, ell))
    if z >= 4:
        if not (col(r + 2, 1) == 0 and col(r + 2, 2) == 1): fails.append(("z4", r, ell))
print("period-lemma tests:", ntests, "failures:", len(fails), fails[:10])
