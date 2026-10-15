# For a driver word u (c values at times t0..t0+len(u)-1), compute col1 at time t0+len(u)
# as a function of the K = len(u)+1 cells (cols 1..K) at time t0.  Report the set of values.
import sys
def step(row, c, K):
    # row: bits of cols 1..K (bit i <-> col i+1); cells beyond K unknown -> we only trust a shrinking cone
    return (((row << 1) | c) ^ (row | (row >> 1)))
def col1_after(u, row):
    for c in u:
        row = step(row, c, None)
    return row & 1
u = [int(ch) for ch in sys.argv[1]]
n = len(u); K = n + 1
vals = {}
for row in range(1 << K):
    v = col1_after(u, row)
    vals.setdefault(v, 0); vals[v] += 1
print(sys.argv[1], 'K=', K, 'col1 value counts:', vals)
