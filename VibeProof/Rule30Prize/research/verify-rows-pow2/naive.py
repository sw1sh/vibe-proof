# Naive rule 30 simulation (dict-free list), cross-check of the claim on small rows.
import sys
T = int(sys.argv[1])
row = {0: 1}
def cell(r, p): return r.get(p, 0)
rows = [dict(row)]
for t in range(1, T+1):
    prev = rows[-1]
    new = {}
    for p in range(-t, t+1):
        v = cell(prev, p-1) ^ (cell(prev, p) | cell(prev, p+1))
        if v: new[p] = 1
    rows.append(new)
center = [cell(rows[t], 0) for t in range(20)]
print("center", center)
def gap(t):
    g = 0
    while cell(rows[t], t-1-g) == 0: g += 1
    return g
def nu2(n):
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k
Jclaim = [0,2,3,5,6,8,14,15,23,24,26,28,33,35,36,38,40,42,47,48,50,53,54,57,59,62,63,65,68,69,71,73,76,78,79,81,83,85]
bad = 0
for t in range(1, T+1):
    if gap(t) != Jclaim[nu2(t)]: bad += 1
print("rows 1..%d: gap != J_{nu2} count:" % T, bad)
# (c): rows 2^k-1
k = 0
while 2**k - 1 <= T:
    t = 2**k - 1
    B = 0
    while cell(rows[t], t - B) == 1: B += 1
    print("k=%d row %d black run %d, J_k+1=%d, ok=%s" % (k, t, B, Jclaim[k]+1, B == Jclaim[k]+1))
    k += 1
