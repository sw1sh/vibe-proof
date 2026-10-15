#!/usr/bin/env python3
"""Does the strip relaxation (columns 1..b exact, column b+1 free) force the period-2 block law?
Center alternates: black at even t, white at odd t. y = column 1 at the white (odd) times.
R_n = strip states at a white time after n double steps from ALL states (decreasing in n).
On the limit set, search for output words 101 (gap 2), 10001 (gap 4), 11 (gap 1), 100000 (gap >= 6)."""
import sys
def step(s, c, x, b):
    full = c | (s << 1) | (x << (b + 1))           # bit 0 = col 0, bit p = col p, bit b+1 = input
    new = 0
    for p in range(1, b + 1):
        new |= (((full >> (p - 1)) & 1) ^ (((full >> p) & 1) | ((full >> (p + 1)) & 1))) << (p - 1)
    return new
def succ2(s, b):   # from a white time: white step (c=0) then black step (c=1)
    out = set()
    for x1 in (0, 1):
        s1 = step(s, 0, x1, b)
        for x2 in (0, 1):
            out.add(step(s1, 1, x2, b))
    return out
def analyse(b, maxn=400):
    R = set(range(1 << b)); n = 0
    succ = {s: succ2(s, b) for s in R}
    while n < maxn:
        R2 = set()
        for s in R: R2 |= succ[s]
        n += 1
        if R2 == R: break
        R = R2
    y = lambda s: s & 1
    def has(word):
        # exists a path s0 -> s1 -> ... in R with y(s_i) = word[i]
        cur = {s for s in R if y(s) == word[0]}
        for ch in word[1:]:
            cur = {u for s in cur for u in succ[s] if u in R and y(u) == ch}
            if not cur: return False
        return True
    res = {w: has([int(c) for c in w]) for w in ('11', '101', '1001', '10001', '100001', '1000001')}
    return n, len(R), res
for b in range(2, int(sys.argv[1]) + 1):
    n, size, res = analyse(b)
    print(f"b={b:2d}: stable after {n:3d} double steps, |R_inf| = {size:6d}; possible output windows: " +
          ', '.join(f"{w}:{'yes' if v else 'no'}" for w, v in res.items()))
