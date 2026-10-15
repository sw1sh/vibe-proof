import sys
# Skeleton of an attractor: for the run (w, n, d, ph0), over the window [S/2, S), for each column k = 0..K and each
# residue r mod Q (relative to phase 0 of w), report the constant value or '*' if it varies.
w = sys.argv[1]; n = int(sys.argv[2]); d = int(sys.argv[3]); ph0 = int(sys.argv[4]); S = int(sys.argv[5])
K = int(sys.argv[6]); Q = int(sys.argv[7])
P = len(w)
def drv(t):
    return (d >> t) & 1 if t < n else int(w[(ph0 + t - n) % P])
row = drv(0)
rows = []
for t in range(n + S):
    if t >= n + S // 2:
        rows.append((t, row))
    Wd = row.bit_length() + 2
    mask = (1 << Wd) - 1
    row = (((row << 1) ^ (row | (row >> 1))) & mask) & ~1 | drv(t + 1)
# residue: phase index of time t is (ph0 + t - n) % P ; use r = (ph0 + t - n) % Q (Q multiple of P)
vals = {}
for (t, rw) in rows:
    r = (ph0 + t - n) % Q
    for k in range(K + 1):
        v = (rw >> k) & 1
        key = (k, r)
        if key not in vals: vals[key] = v
        elif vals[key] != v: vals[key] = '*'
print('phase-0 aligned, rows = residues r mod %d (w[r mod P]), columns 0..%d' % (Q, K))
for r in range(Q):
    print('%2d %s | %s' % (r, w[r % P], ''.join(str(vals[(k, r)]) if vals[(k, r)] != '*' else '*' for k in range(1, K + 1))))
