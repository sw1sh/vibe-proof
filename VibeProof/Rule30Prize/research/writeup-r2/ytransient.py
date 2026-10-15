#!/usr/bin/env python3
"""Index of the last gap that is not 3 or 5 (white-time samples), for y_out.txt and for fresh runs."""
import sys, random
def last_bad(y):
    pos = [i for i, v in enumerate(y) if v]
    bad = [pos[i+1] for i in range(len(pos)-1) if pos[i+1]-pos[i] not in (3, 5)]
    return (bad[-1] if bad else None), len(y)
s = open('../synth-r2/y_out.txt').read().strip()
print('y_out.txt (T0=2000, phase 0): last non-{3,5} gap ends at sample', last_bad([int(c) for c in s]))
def run(T0, N, ph, mode):
    if mode == 0:
        off = T0 + 2; r = 1 << off
        for t in range(T0): r = (r << 1) ^ (r | (r >> 1))
        a = (r >> off) & ~1
    else:
        rnd = random.Random(T0); a = sum(rnd.getrandbits(1) << p for p in range(1, T0 + 1))
    y = []
    for t in range(N):
        c = (t + ph) & 1
        a = (a & ~1) | c
        if c == 0: y.append((a >> 1) & 1)
        a = ((a << 1) ^ (a | (a >> 1))) & ~1
    return y
for args in [(2000, 30000, 0, 0), (2000, 30000, 1, 0), (777, 30000, 0, 0), (3000, 30000, 1, 0), (500, 30000, 0, 1), (1500, 30000, 1, 1), (5000, 30000, 0, 0)]:
    print(args, 'last non-{3,5} gap ends at sample', last_bad(run(*args)))
