"""Lemma A, Lemma A* and black_stays on the real rule-30 pattern from a single black cell.
Rows are big ints; bit i <-> position p = i - OFF.
"""
import sys
from collections import deque

T = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
JMAX = 3
OFF = T + 2
W = 2 * T + 5
MASK = (1 << W) - 1

row = 1 << OFF
hist = deque(maxlen=9 * JMAX)
counts = {j: 0 for j in range(1, JMAX + 1)}
fails = {j: 0 for j in range(1, JMAX + 1)}
c0, c1 = [], []
for t in range(T):
    # check Lemma A* (j = 1 is Lemma A) at time t using the previous 9j rows
    for j in range(1, JMAX + 1):
        if len(hist) >= 9 * j:
            A = MASK
            for k in range(1, 9 * j + 1):
                A &= hist[-k]
            if A:
                counts[j] += bin(A).count("1")
                for i in range(1, j + 1):
                    if (A << (2 * i - 1)) & row:            # column m+2i-1 must be white
                        fails[j] += 1
                    if (A << (2 * i)) & (~row & MASK):     # column m+2i must be black
                        fails[j] += 1
    c0.append((row >> OFF) & 1)
    c1.append((row >> (OFF + 1)) & 1)
    hist.append(row)
    row = ((row << 1) ^ (row | (row >> 1))) & MASK  # new[p] = old[p-1] xor (old[p] or old[p+1])

print("center prefix", ''.join(map(str, c0[:20])))
for j in counts:
    print(f"Lemma A* j={j}: instances (t, m) with column m black 9j steps = {counts[j]}, failures = {fails[j]}")

# black run >= 9 in column 0 followed by white run of length r: col1 = 0 at e, 1 at e+1..e+r
inst = bad = 0
t = 0
while t < T:
    if c0[t] == 1:
        u = t
        while u < T and c0[u] == 1:
            u += 1
        s = u - t
        e = u
        v = e
        while v < T and c0[v] == 0:
            v += 1
        r = v - e
        if s >= 9 and v < T and r >= 1:
            inst += 1
            if c1[e] != 0 or any(c1[e + i] != 1 for i in range(1, r + 1)):
                bad += 1
        t = u
    else:
        t += 1
print(f"center: black runs >= 9 followed by a white run (t < {T}): {inst}, black_stays failures = {bad}")
