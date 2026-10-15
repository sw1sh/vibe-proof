# Verify on the true rule-30 pattern: whenever cell(t..t+8, i) are all 1, cell(t+9, i+1) = 0 and cell(t+9, i+2) = 1.
import sys
N = int(sys.argv[1])
W = 2 * N + 8
off = N + 4
row = 1 << off
rows = []
for t in range(N + 12):
    rows.append(row)
    row = ((row << 1) ^ (row | (row >> 1))) & ((1 << W) - 1)
def cell(t, p): return (rows[t] >> (off - p)) & 1   # bit (off - p) <-> position p? use consistent orientation
# orientation: new = left xor (center or right). In the int, (row << 1) moves bit b to b+1.
# new bit b = old bit (b-1) xor (old b or old b+1).  So 'left' neighbor of bit b is bit b-1.
# Map position p -> bit off + p would make left = p-1 -> bit off+p-1 = b-1. Use that.
def cell(t, p): return (rows[t] >> (off + p)) & 1
# sanity: center column start 1,1,0,1,1,1,0,0,1,1
print('center', ''.join(str(cell(t, 0)) for t in range(20)))
cnt = 0; bad = 0
for t in range(N - 10):
    for p in range(-t - 1, t + 2):
        if all(cell(t + s, p) for s in range(9)):
            cnt += 1
            if not (cell(t + 9, p + 1) == 0 and cell(t + 9, p + 2) == 1): bad += 1
print('occurrences', cnt, 'violations', bad)
