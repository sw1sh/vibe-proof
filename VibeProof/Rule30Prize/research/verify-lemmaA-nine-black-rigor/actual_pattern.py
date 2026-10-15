# Rule 30 from a single black cell, rows as big ints: bit (p + OFF) = cell(t, p).
# new_p = cell(p-1) xor (cell(p) or cell(p+1))  ->  new = (row << 1) ^ (row | (row >> 1))
import sys
T = int(sys.argv[1])
OFF = T + 5
row = 1 << OFF
rows = [row]
# center column sanity check vs OEIS A051023 first terms
A051023 = [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1]
r = row; cen = []
for t in range(len(A051023)):
    cen.append((r >> OFF) & 1); r = (r << 1) ^ (r | (r >> 1))
assert cen == A051023, cen
print("center column matches A051023 prefix")
from collections import deque
win = deque([row])
n9 = 0; v9a = 0; v9b = 0; n8 = 0; v8a = 0; v8b = 0; first8 = None
r = row
for t in range(1, 10): r = (r << 1) ^ (r | (r >> 1)); win.append(r)
# win holds rows t..t+9 for t = 0
t = 0
while t + 9 <= T:
    rows_ = list(win)
    B8 = rows_[0]
    for i in range(1, 8): B8 &= rows_[i]
    B9 = B8 & rows_[8]
    r9 = rows_[9]; r8 = rows_[8]
    n9 += bin(B9).count("1")
    v9a += bin(B9 & (r9 >> 1)).count("1")          # cell(t+9,m+1) = 1
    v9b += bin(B9 & ~(r9 >> 2)).count("1")         # cell(t+9,m+2) = 0
    n8 += bin(B8).count("1")
    x = B8 & (r8 >> 1)                              # cell(t+8,m+1) = 1 after 8 blacks t..t+7
    y = B8 & ~(r8 >> 2)                             # cell(t+8,m+2) = 0
    v8a += bin(x).count("1"); v8b += bin(y).count("1")
    if first8 is None and (x or y):
        z = x | y
        m = (z & -z).bit_length() - 1 - OFF
        first8 = (t, m, (x >> (m + OFF)) & 1, (y >> (m + OFF)) & 1)
    r = (r << 1) ^ (r | (r >> 1)); win.popleft(); win.append(r); t += 1
print(f"T={T}: windows with 9 blacks: {n9}; violations (m+1 black): {v9a}, (m+2 white): {v9b}")
print(f"        windows with 8 blacks: {n8}; 8-black failures (m+1 black): {v8a}, (m+2 white): {v8b}; first {first8}")
