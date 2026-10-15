import sys
# Simulate the driven right half from empty, driver = d (n bits little-endian) then w^inf from phase ph0.
# Report periodicity of column k sequences (k=1..K) over the tail, and of column 1 at white phases.
w = sys.argv[1]; n = int(sys.argv[2]); d = int(sys.argv[3]); ph0 = int(sys.argv[4]); steps = int(sys.argv[5])
K = int(sys.argv[6]) if len(sys.argv) > 6 else 12
P = len(w)
def drv(t):
    return (d >> t) & 1 if t < n else int(w[(ph0 + t - n) % P])
row = drv(0)  # bit p = column p
cols = [[] for _ in range(K + 1)]
cs = []
for t in range(steps):
    for k in range(K + 1):
        cols[k].append((row >> k) & 1)
    cs.append(row & 1)
    W_ = row.bit_length() + 2
    mask = (1 << W_) - 1
    new = ((row << 1) ^ (row | (row >> 1))) & mask
    new = (new & ~1) | drv(t + 1)
    row = new
def eventual_period(seq, start):
    L = len(seq)
    for p in range(1, (L - start) // 3):
        if all(seq[i] == seq[i + p] for i in range(start, L - p)):
            return p
    return None
half = steps // 2
for k in range(1, K + 1):
    print('col', k, 'tail period', eventual_period(cols[k], half))
# column 1 at white phases: times t >= n with w[phase] == '0'
white = [cols[1][t] for t in range(half, steps) if t >= n and w[(ph0 + t - n) % P] == '0']
print('col1 at white phases, tail period (in white-count):', eventual_period(white, 0))
print('width at end', row.bit_length())
# show a window of the space-time diagram near the boundary
t0 = int(sys.argv[7]) if len(sys.argv) > 7 else steps - 40
for t in range(t0, min(steps, t0 + 40)):
    print('%6d %s|%s' % (t, cols[0][t], ''.join('#' if cols[k][t] else '.' for k in range(1, K + 1))))
