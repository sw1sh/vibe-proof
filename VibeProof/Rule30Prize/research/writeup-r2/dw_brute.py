#!/usr/bin/env python3
"""Brute-force D(W) for small W: max over ZBL rows supported on depths 1..W of the first even time t with
column -1 (depth 1) white. Independent of the C programs (bit k-1 = depth k, wall white)."""
import sys
def first_violation(x, cap=400):
    for t in range(cap):
        if t % 2 == 0 and not (x & 1): return t
        x = (x >> 1) ^ (x | (x << 1))      # depth 0 (wall) contributes 0
    return None
for W in range(1, int(sys.argv[1]) + 1):
    best = max(first_violation(x) for x in range(1 << W))
    print(W, best, end='; ')
print()
