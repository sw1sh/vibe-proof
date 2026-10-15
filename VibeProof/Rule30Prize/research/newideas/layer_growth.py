# Width of the eventually-periodic boundary layer vs time, right half driven by w^inf.
import sys, random
def rows_right(cvals, init):
    row = init; rows = []
    W = max(init.bit_length(), 1) + len(cvals) + 2
    mask = (1 << W) - 1
    for t, ct in enumerate(cvals):
        rows.append(row)
        row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
    return rows
w = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3]); initw = int(sys.argv[4])
random.seed(seed)
init = random.getrandbits(initw) if seed else 0
P = len(w)
c = [int(w[t % P]) for t in range(steps)]
rows = rows_right(c, init)
# layer width at time window [a, a+L): largest k such that columns 1..k are periodic with period Q | 8P on the window
def width_at(a, L=400, Q=None):
    k = 0
    while True:
        p = k + 1
        s = [(rows[t] >> (p - 1)) & 1 for t in range(a, a + L)]
        ok = False
        for Qc in ([Q] if Q else [P * m for m in (1, 2, 4, 8)]):
            if all(s[i] == s[i + Qc] for i in range(L - Qc)): ok = True; break
        if not ok: return k
        k += 1
        if k > 2000: return k
for a in range(0, steps - 400, (steps - 400) // 12):
    print(a, width_at(a), end=' | ')
print()
