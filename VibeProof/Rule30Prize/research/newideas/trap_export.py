# Compute the trap for word w at strip width b: reachable set (in the strip relaxation with free input)
# from an actual absorbed strip state; verify that every node in it keeps col_1|zeros on one periodic
# pattern (consistent position labelling) and that it is closed. Export as text: phase state pos.
import sys, random
from collections import deque
w = sys.argv[1]; b = int(sys.argv[2]); seed = int(sys.argv[3]); out = sys.argv[4]
P = len(w)
random.seed(seed)
def evolve(row, t0, n):
    W = row.bit_length() + n + 4; mask = (1 << W) - 1
    rows = []
    for t in range(t0, t0 + n):
        rows.append(row)
        ct = int(w[t % P])
        row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
    return rows
rows = evolve(random.getrandbits(300), 0, 4600)
t0 = 4000 - 4000 % P   # phase 0 time
bmask = (1 << b) - 1
def succs(phi, s):
    cphi = int(w[phi % P])
    bit = lambda x, p: ((x >> (p - 1)) & 1) if p >= 1 else cphi
    base = 0
    for p in range(1, b):
        base |= (bit(s, p - 1) ^ (bit(s, p) | bit(s, p + 1))) << (p - 1)
    if bit(s, b) == 1:
        return [base | ((1 ^ bit(s, b - 1)) << (b - 1))]
    return [base, base | (1 << (b - 1))]
start = (t0 % P, rows[t0] & bmask)
seen = {start}; dq = deque([start])
while dq:
    ph, s = dq.popleft()
    for s2 in succs(ph, s):
        key = ((ph + 1) % P, s2)
        if key not in seen: seen.add(key); dq.append(key)
# output labelling: find period word from the actual trajectory
outw = [rows[t] & 1 for t in range(t0, t0 + 64 * P) if w[t % P] == '0']
L = len(outw)
m = next(d for d in range(1, L) if all(outw[i] == outw[i + d] for i in range(L - d)))
u = outw[:m]
pos = {start: 0}; dq = deque([start]); ok = True
while dq and ok:
    x = dq.popleft(); ph, s = x
    if w[ph] == '0':
        if (s & 1) != u[pos[x] % m]: ok = False; break
        npos = (pos[x] + 1) % m
    else: npos = pos[x]
    for s2 in succs(ph, s):
        y = ((ph + 1) % P, s2)
        if y in pos:
            if pos[y] != npos: ok = False; break
        else: pos[y] = npos; dq.append(y)
print(f"w={w} b={b}: reachable set size {len(seen)}, closed by construction, output-consistent: {ok}, output period word {''.join(map(str,u))}")
with open(out, 'w') as f:
    f.write(f"{w} {b} {len(seen)}\n")
    for (ph, s) in sorted(seen):
        f.write(f"{ph} {s} {pos[(ph, s)]}\n")
