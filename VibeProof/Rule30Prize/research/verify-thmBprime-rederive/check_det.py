# Independent brute-force re-derivation of the finite facts used by Theorem B'.
# Rule 30: new = left XOR (center OR right).
import itertools, sys

def rule(l, c, r):
    return l ^ (c | r)

def evolve_right(row, drivers):
    """row: values at columns 1..L at time e (list of 0/1).
    drivers: values of column 0 at times e, e+1, ..., e+n-1.
    Returns column-1 values at times e .. e+n (n+1 values), computed on the
    shrinking light cone (requires L >= n+1)."""
    assert len(row) >= len(drivers) + 1
    cur = list(row)
    out = [cur[0]]
    for d in drivers:
        nxt = []
        for i in range(len(cur) - 1):
            left = d if i == 0 else cur[i - 1]
            nxt.append(rule(left, cur[i], cur[i + 1]))
        cur = nxt
        out.append(cur[0])
    return out

# ---- Lemma A: 9 black steps of the left neighbour force (0,1) in the next two columns
okA = all(evolve_right(list(bits), [1] * 9)[-1] == 0 for bits in itertools.product([0, 1], repeat=11))
# need column 2 too: track the full row
def lemmaA_full():
    for bits in itertools.product([0, 1], repeat=11):
        cur = list(bits)
        for _ in range(9):
            cur = [rule(1 if i == 0 else cur[i - 1], cur[i], cur[i + 1]) for i in range(len(cur) - 1)]
        if cur != [0, 1]:
            return False
    return True
print("Lemma A (all 2^11 rows):", lemmaA_full())
# is 9 minimal? (8 steps with 10 cells)
def lemmaA_k(k):
    for bits in itertools.product([0, 1], repeat=k + 2):
        cur = list(bits)
        for _ in range(k):
            cur = [rule(1 if i == 0 else cur[i - 1], cur[i], cur[i + 1]) for i in range(len(cur) - 1)]
        if cur != [0, 1]:
            return False
    return True
print("Lemma A with 8 steps would hold:", lemmaA_k(8))

def determined(u, j0):
    """u: tuple of 0/1. Every row of length |u|+10 whose first 2*j0 cells read (0 1)^j0
    gives the same column-1 trace under driver u ++ 1^9."""
    L = len(u) + 10
    if 2 * j0 > L:
        return None
    drv = list(u) + [1] * 9
    pref = [0, 1] * j0
    traces = set()
    for tail in itertools.product([0, 1], repeat=L - 2 * j0):
        traces.add(tuple(evolve_right(pref + list(tail), drv)))
        if len(traces) > 1:
            return False
    return True

blocks = []
for n in range(1, 8):
    for mid in itertools.product([0, 1], repeat=max(0, n - 2)):
        if n == 1:
            blocks.append((0,))
        else:
            blocks.append((0,) + mid + (0,))
blocks = sorted(set(blocks), key=lambda b: (len(b), b))
print("number of blocks:", len(blocks))

table = {}
with open(sys.argv[1]) as f:
    for line in f:
        line = line.strip()
        if not line:
            continue
        w, j = line.split(':')
        table[tuple(int(ch) for ch in w.strip())] = int(j)
print("table entries:", len(table), "same set as blocks:", set(table) == set(blocks))

from collections import Counter
cnt = Counter()
mismatch = []
all4 = True
for u in blocks:
    mj = None
    for j0 in range(0, (len(u) + 10) // 2 + 1):
        if determined(u, j0):
            mj = j0
            break
    cnt[mj] += 1
    if mj != table.get(u):
        mismatch.append((u, mj, table.get(u)))
    if not determined(u, 4):
        all4 = False
    # monotonicity sanity: determined for all j0 >= mj
    for j in range(mj, (len(u) + 10) // 2 + 1):
        if not determined(u, j):
            print("non-monotone!", u, j)
print("minimal j0 histogram:", dict(cnt))
print("mismatches vs table:", mismatch)
print("Determined(u,4) for all 64 blocks:", all4)
