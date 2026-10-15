import sys
# Track formation of the attractor: compute final pattern (columns 1..K, period Q) from the tail, then for each time
# window of length Q report how many leading columns agree with the final pattern throughout the window,
# and the largest K' such that columns 1..K' agree (agreement depth), printed every `every` windows.
w = sys.argv[1]; n = int(sys.argv[2]); d = int(sys.argv[3]); ph0 = int(sys.argv[4]); S = int(sys.argv[5])
K = int(sys.argv[6]); Q = int(sys.argv[7]); every = int(sys.argv[8])
P = len(w)
def drv(t):
    return (d >> t) & 1 if t < n else int(w[(ph0 + t - n) % P])
row = drv(0)
rows = []
for t in range(n + S):
    rows.append(row)
    Wd = row.bit_length() + 2
    mask = (1 << Wd) - 1
    row = (((row << 1) ^ (row | (row >> 1))) & mask) & ~1 | drv(t + 1)
T = n + S
# final pattern from the last 4Q steps
fin = {}
for t in range(T - 4 * Q, T):
    r = (ph0 + t - n) % Q
    fin.setdefault(r, rows[t] >> 1)
# zone width of the final pattern
def agree(t):
    r = (ph0 + t - n) % Q
    x = (rows[t] >> 1) ^ fin[r]
    k = 0
    while k < K and not (x >> k) & 1: k += 1
    return k
line = []
for t0 in range(n, T - Q, Q):
    a = min(agree(t) for t in range(t0, t0 + Q))
    line.append(a)
for i in range(0, len(line), every):
    chunk = line[i:i + every]
    print('t=%6d  %s' % (n + i * Q, ' '.join('%2d' % x for x in chunk)))
