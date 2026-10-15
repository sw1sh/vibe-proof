# On the true rule-30 pattern: whenever column p has the block u at times t..t+|u|-1, check that
# cell(t+|u|, p+1) OR cell(t+|u|, p+2) == 1  (forcing of e_1), and report counts.
import sys
N = int(sys.argv[1]); u = [int(ch) for ch in sys.argv[2]]
W = 2 * N + 8; off = N + 4
row = 1 << off; rows = []
for t in range(N + 2):
    rows.append(row)
    row = ((row << 1) ^ (row | (row >> 1))) & ((1 << W) - 1)
def cell(t, p): return (rows[t] >> (off + p)) & 1
L = len(u); cnt = 0; viol = 0
for t in range(N - L - 1):
    for p in range(-t - 1, t + 2):
        if all(cell(t + s, p) == u[s] for s in range(L)):
            cnt += 1
            if not (cell(t + L, p + 1) | cell(t + L, p + 2)): viol += 1
print(sys.argv[2], 'occurrences', cnt, 'violations of e1=1:', viol)
