"""
Independent brute-force check of the finite facts behind Theorem B.

Setting: half-line of columns p = 1, 2, 3, ... driven by a boundary column 0 whose
values are given externally.  Rule 30 update for p >= 1:
    new(p) = old(p-1) xor (old(p) or old(p+1)),  old(0) = driver value at that time.

Light cone: after k steps, columns 1..W-k are determined by the initial columns 1..W
and the k driver values.

Checks:
 (1) absorbing: if driver=1 and (x1,x2)=(0,1) then next (x1,x2)=(0,1)  [any x3]
 (2) pair lemma: for k steps of driver 1, from ANY initial state of columns 1..k+2,
     (x1,x2) after k steps is (0,1).  Find the minimal such k.
 (3) single-cell lemma: after k steps of driver 1, x1 = 0 for every initial state.
     Find the minimal such k.
"""
import itertools, sys

def step(row, d):
    # row: tuple of known cells at columns 1..W ; returns columns 1..W-1
    W = len(row)
    out = []
    for i in range(W - 1):  # column i+1
        left = d if i == 0 else row[i - 1]
        out.append(left ^ (row[i] | row[i + 1]))
    return tuple(out)

def run(row, drivers):
    for d in drivers:
        row = step(row, d)
    return row

# (1) absorbing
for x3 in (0, 1):
    r = step((0, 1, x3), 1)
    assert r[:2] == (0, 1), (x3, r)
print("absorbing (0,1) under driver 1: OK")

# (2) pair lemma minimal k
def pair_ok(k):
    W = k + 2
    bad = 0
    for bits in itertools.product((0, 1), repeat=W):
        r = run(bits, [1] * k)
        assert len(r) == 2
        if r != (0, 1):
            bad += 1
    return bad

for k in range(1, 13):
    b = pair_ok(k)
    print(f"pair lemma k={k}: failing initial states = {b}")
    if b == 0:
        print("minimal k for pair lemma:", k)
        break

# (3) single-cell lemma minimal k
def single_ok(k):
    W = k + 1
    bad = 0
    for bits in itertools.product((0, 1), repeat=W):
        r = run(bits, [1] * k)
        assert len(r) == 1
        if r[0] != 0:
            bad += 1
    return bad

for k in range(1, 13):
    b = single_ok(k)
    print(f"single-cell lemma k={k}: failing initial states = {b}")
    if b == 0:
        print("minimal k for single-cell lemma:", k)
        break

# Also verify specifically k=9 for both, with full enumeration
assert pair_ok(9) == 0
assert single_ok(9) == 0
print("k=9 verified for pair lemma (2^11 states) and single-cell lemma (2^10 states)")
