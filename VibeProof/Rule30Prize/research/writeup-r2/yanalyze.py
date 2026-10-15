#!/usr/bin/env python3
"""Analyze synth-r2/y_out.txt: column 1 at the white times of a right half driven by an alternating center."""
import sys, collections
s = open(sys.argv[1]).read().strip()
skip = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
y = s[skip:]
n = len(y); ones = y.count('1')
print(f"length {len(s)}, analysed from index {skip}: n={n}, ones={ones}, density={ones/n:.6f}, 3/14={3/14:.6f}, 3n/14={3*n/14:.1f}, diff={ones-3*n/14:.1f}")
# gaps between consecutive ones
pos = [i for i, c in enumerate(y) if c == '1']
gaps = [b - a for a, b in zip(pos, pos[1:])]
print("gap histogram:", sorted(collections.Counter(gaps).items()))
# blocks: split at ones -> words '1' + zeros
blocks = ['1' + '0' * (g - 1) for g in gaps]
# run-length of consecutive 5-gaps between non-5 gaps
runs = []; r = 0
for g in gaps:
    if g == 5: r += 1
    else: runs.append((r, g)); r = 0
print("(number of 5-gaps before each non-5 gap, that gap) histogram:", sorted(collections.Counter(runs).items())[:40])
# prefix discrepancy
D = 0; mn = mx = 0
for c in y:
    D += (1 if c == '1' else 0) - 3/14
    mn = min(mn, D); mx = max(mx, D)
print(f"prefix discrepancy of ones - 3/14 per sample: range [{mn:.2f}, {mx:.2f}]")
# factor complexity for small n
for L in (4, 8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64):
    print(f"p({L})={len(set(y[i:i+L] for i in range(n - L + 1)))}", end='  ')
print()
# eventual periodicity test: smallest p with y[i]=y[i+p] for all i in the last half
half = y[n//2:]
per = next((p for p in range(1, len(half)//3) if half[:-p] == half[p:]), None)
print("period of last half (None = not periodic within n/6):", per)
