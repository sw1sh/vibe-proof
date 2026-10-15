# Mechanism check on the driven right half (columns >= 1), arbitrary initial right-half state:
# driver c(t1+n) = w[n mod P], w = 1^r u, r = 9*ceil((|u|+9)/2) (threshold).
# Claim (proof steps 1-5): column 1 is periodic with period P from e = t1 + r, i.e. exactly from e.
# Also report the first time from which column 1 is periodic (to see the bound is not vacuous).
import random
from math import ceil
random.seed(12345)

def simulate(w, init_bits, W, steps):
    P = len(w)
    mask = (1 << W) - 1
    row = init_bits & mask
    col1 = []
    for t in range(steps):
        col1.append(row & 1)
        c = w[t % P]
        row = (((row << 1) | c) ^ (row | (row >> 1))) & mask
    return col1

us = ["0", "00", "010", "0110", "0000000", "01010101", "1", "0101", "0011", "000000000",
      "0100110", "1111111110", "0" * 15, "011010011001", "1001"]
tot_fail = 0
for u in us:
    d = len(u)
    j = ceil((d + 9) / 2)
    r = 9 * j
    w = [1] * r + [int(ch) for ch in u]
    P = len(w)
    steps = r + 8 * P
    W = steps + 4
    fails = 0
    latest = 0
    for trial in range(60):
        init = random.getrandbits(W)
        col1 = simulate(w, init, W, steps)
        e = r  # t1 = 0
        for t in range(e, steps - P):
            if col1[t] != col1[t + P]:
                fails += 1
                break
        # first time T1 from which col1 is P-periodic (within horizon)
        T1 = steps - P
        while T1 > 0 and col1[T1 - 1] == col1[T1 - 1 + P]:
            T1 -= 1
        latest = max(latest, T1)
    # threshold minus one (r-1 with same u) to see whether the bound is sharp for the mechanism
    w2 = [1] * (r - 1) + [int(ch) for ch in u]
    P2 = len(w2)
    steps2 = (r - 1) + 8 * P2
    W2 = steps2 + 4
    nonper = 0
    for trial in range(60):
        init = random.getrandbits(W2)
        col1 = simulate(w2, init, W2, steps2)
        if any(col1[t] != col1[t + P2] for t in range(r - 1, steps2 - P2)):
            nonper += 1
    tot_fail += fails
    print(f"u={u!r:16} r={r:3} P={P:3}: periodic-from-e failures {fails}/60; latest onset {latest} (e={r});"
          f" with r-1: not periodic-from-e in {nonper}/60")
print("TOTAL failures:", tot_fail)
