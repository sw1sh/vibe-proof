import sys
w = sys.argv[1]; q = int(sys.argv[2]); u = int(sys.argv[3]); ph0 = int(sys.argv[4]); S = int(sys.argv[5]); K = int(sys.argv[6])
P = len(w); Wd = S + 300
row = 0
for p in range(1, Wd):
    if (u >> ((p - 1) % q)) & 1: row |= 1 << p
row |= int(w[ph0])
mask = (1 << Wd) - 1
cols = [[] for _ in range(K + 1)]
for t in range(S):
    for k in range(K + 1): cols[k].append((row >> k) & 1)
    row = ((((row << 1) ^ (row | (row >> 1))) & mask) & ~1) | int(w[(ph0 + t + 1) % P])
def per(seq, start):
    L = len(seq)
    for p in range(1, (L - start) // 3):
        if all(seq[i] == seq[i + p] for i in range(start, L - p)): return p
    return None
print('column periods over second half:', [per(cols[k], S // 2) for k in range(1, K + 1)])
white = [cols[1][t] for t in range(S // 2, S) if w[(ph0 + t) % P] == '0']
print('col1 at white phases period:', per(white, 0))
for t in range(S - 16, S):
    print('%5d %s|%s' % (t, cols[0][t], ''.join('#' if cols[k][t] else '.' for k in range(1, K + 1))))
