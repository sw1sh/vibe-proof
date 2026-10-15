"""
Exhaustive check of Lemma A* for j = 1 and j = 2 by bit-slicing:
after 9j steps of driver 1, columns 1..2j read (0,1)^j for EVERY initial state of
columns 1..W, W = 9j + 2j (the light cone of columns 1..2j after 9j steps).

Each column is represented by a Python int with 2^W bits; bit n of column i is
bit i of n, so all 2^W initial states are processed simultaneously.
Also checks that 9j-1 steps do NOT suffice (sanity check that the test can fail).
"""
import sys

def column_masks(W):
    N = 1 << W
    masks = []
    for i in range(W):
        # pattern: 2^i zeros then 2^i ones, repeated
        block = ((1 << (1 << i)) - 1) << (1 << i)  # 2^(i+1) bits: high half ones
        period = 1 << (i + 1)
        # replicate block to N bits by doubling
        m = block
        length = period
        while length < N:
            m = m | (m << length)
            length *= 2
        masks.append(m)
    return masks, (1 << N) - 1

def simulate(W, steps):
    cols, ALL = column_masks(W)
    for _ in range(steps):
        new = []
        for i in range(len(cols) - 1):
            left = ALL if i == 0 else cols[i - 1]  # driver = 1
            new.append(left ^ (cols[i] | cols[i + 1]))
        cols = new
    return cols, ALL

def check(j, steps):
    W = steps + 2 * j
    cols, ALL = simulate(W, steps)
    assert len(cols) == 2 * j
    ok = True
    for i in range(2 * j):
        want = 0 if i % 2 == 0 else ALL
        if cols[i] != want:
            ok = False
    return ok, W

for j in (1, 2):
    ok, W = check(j, 9 * j)
    print(f"j={j}: {9*j} steps, W={W}, all 2^{W} states give (0,1)^{j}: {ok}")
    ok2, W2 = check(j, 9 * j - 1)
    print(f"j={j}: {9*j-1} steps, W={W2}, all states give (0,1)^{j}: {ok2}")
