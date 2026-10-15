#!/usr/bin/env python3
"""Independent check (strip relaxation, columns 1..b exact, column b+1 arbitrary at every step) of the claim:
if the center alternates (black at even t, white at odd t), column 1 cannot be white at K consecutive odd times.
Prints, for each b, the largest K for which some strip history achieves K consecutive white odd times (capped)."""
import itertools
def step(s, c, x, b):
    cells = [c] + list(s) + [x]
    return tuple(cells[p - 1] ^ (cells[p] | cells[p + 1]) for p in range(1, b + 1))
def maxK(b, cap=12):
    # states at an odd time with column 1 white
    cur = {s for s in itertools.product((0, 1), repeat=b) if s[0] == 0}
    K = 1
    while cur and K < cap:
        nxt = set()
        for s in cur:
            for x1 in (0, 1):
                s1 = step(s, 0, x1, b)          # odd time: center white
                for x2 in (0, 1):
                    s2 = step(s1, 1, x2, b)     # even time: center black
                    if s2[0] == 0: nxt.add(s2)
        if not nxt: return K
        cur = nxt; K += 1
    return K
for b in range(1, 9):
    print(f"b={b}: max consecutive white odd times for column 1 = {maxK(b)}")
