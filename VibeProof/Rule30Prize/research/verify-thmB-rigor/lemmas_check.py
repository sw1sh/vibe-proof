# Independent brute-force checks of Lemma A (j=1) and Lemma A* (j=2),
# and the arithmetic equivalence ceil((P-r+9)/2) == (P-r+10)//2 and the 0.82P+8.2 claim.
import itertools, sys
import numpy as np

def rule(l, c, r):
    return l ^ (c | r)

def run_black(row, k):
    # row: list of bits for columns m+1..m+n at time t; column m black for k steps.
    for _ in range(k):
        left = 1
        new = []
        for i in range(len(row) - 1):
            new.append(rule(left, row[i], row[i + 1]))
            left = row[i]
        row = new
    return row

# Lemma A: 9 black steps, 11 columns -> columns m+1,m+2 at t+9 are (0,1)
bad = 0
for bits in itertools.product([0, 1], repeat=11):
    if run_black(list(bits), 9) != [0, 1]:
        bad += 1
print("Lemma A failures over 2^11 rows:", bad)
# 8 steps not enough (sanity: Lemma A is tight-ish)
vals = set()
for bits in itertools.product([0, 1], repeat=10):
    vals.add(run_black(list(bits), 8)[0])
print("after 8 black steps column m+1 takes values:", sorted(vals))

# Lemma A* with j=2: 18 black steps; columns m+1..m+4 at t+18 read 0,1,0,1.
# Light cone: need 4+18 = 22 columns. Vectorized over all 2^22 rows.
n = 22
N = 1 << n
idx = np.arange(N, dtype=np.uint32)
rows = [((idx >> i) & 1).astype(np.uint8) for i in range(n)]  # rows[i] = column m+1+i
for step in range(18):
    new = []
    for i in range(len(rows) - 1):
        left = np.ones(N, dtype=np.uint8) if i == 0 else rows[i - 1]
        new.append(left ^ (rows[i] | rows[i + 1]))
    rows = new
assert len(rows) == 4
ok = all(np.all(rows[i] == v) for i, v in enumerate([0, 1, 0, 1]))
print("Lemma A* (j=2) holds on all 2^22 rows:", ok)

# Arithmetic: ceil((P-r+9)/2) == (P-r+10)//2 for r<=P; and r >= 0.82P+8.2 => condition.
from math import ceil
viol = 0
for P in range(1, 3000):
    for r in range(0, P + 1):
        a = ceil((P - r + 9) / 2)
        b = (P - r + 10) // 2
        assert a == b
        if r >= 0.82 * P + 8.2 and not (9 * a <= r):
            viol += 1
print("0.82P+8.2 sufficiency violations (P<3000):", viol)
# minimal r for each P vs (9P+90)/11
worst = max((min([r for r in range(P + 1) if 9 * ((P - r + 10) // 2) <= r] or [None]) or 0) - (9 * P + 90) / 11 for P in range(45, 3000))
print("max (minimal admissible r) - (9P+90)/11 over 45<=P<3000:", worst)
