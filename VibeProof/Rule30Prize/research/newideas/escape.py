# In the strip relaxation (columns 1..b, column b+1 free), starting from actual absorbed strip states,
# find the shortest escape: a path where columns 1..L leave the periodic layer pattern.
import sys, random
from collections import deque
w = sys.argv[1]; b = int(sys.argv[2]); L = int(sys.argv[3]); seed = int(sys.argv[4])
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
rows = evolve(random.getrandbits(300), 0, 4000)
t0 = 3000
Lmask = (1 << L) - 1
ref = [rows[t0 + i] & Lmask for i in range(512)]
per = next(Q for Q in range(P, 257, P) if all(ref[i] == ref[i + Q] for i in range(256)))
bmask = (1 << b) - 1
def succs(phi, s):
    cphi = int(w[phi % P])
    bit = lambda x, p: ((x >> (p - 1)) & 1) if p >= 1 else cphi
    base = 0
    for p in range(1, b):
        base |= (bit(s, p - 1) ^ (bit(s, p) | bit(s, p + 1))) << (p - 1)
    if bit(s, b) == 1:
        return [(base | ((1 ^ bit(s, b - 1)) << (b - 1)), None)]
    # free: new col b = col_{b-1} xor col_{b+1}  -> input value of col_{b+1}
    out = []
    for inp in (0, 1):
        v = bit(s, b - 1) ^ inp
        out.append((base | (v << (b - 1)), inp))
    return out
# BFS over (time offset mod per, strip state) from the actual strip state at t0
start = (0, rows[t0] & bmask)
prev = {start: None}
dq = deque([start]); found = None
while dq:
    ph, s = dq.popleft()
    for s2, inp in succs(t0 + ph, s):
        nph = (ph + 1) % per
        if (s2 & Lmask) != ref[(ph + 1) % per]:
            found = ((ph, s), (nph, s2), inp); break
        key = (nph, s2)
        if key not in prev:
            prev[key] = ((ph, s), inp); dq.append(key)
    if found: break
if not found:
    print(f"b={b}: NO escape from the layer within the strip relaxation (reachable set size {len(prev)})")
else:
    # reconstruct path
    path = []; node = found[0]
    while prev[node] is not None:
        pnode, inp = prev[node]; path.append(inp); node = pnode
    path = path[::-1] + [found[2]]
    print(f"b={b}: escape after {len(path)} steps; reachable states {len(prev)}; column-{b+1} inputs needed: {path}")
