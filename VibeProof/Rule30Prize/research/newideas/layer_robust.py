# Robustness of the absorbed layer: take an absorbed state, randomize everything at positions >= k,
# evolve, and test whether columns 1..L stay periodic (layer survives) or break.
import sys, random
w = sys.argv[1]; k = int(sys.argv[2]); trials = int(sys.argv[3]); L = int(sys.argv[4]); horizon = int(sys.argv[5])
P = len(w)
random.seed(12345)
def evolve(row, t0, n, record=0):
    W = row.bit_length() + n + 4; mask = (1 << W) - 1
    cols = []
    for t in range(t0, t0 + n):
        if record: cols.append(row & ((1 << record) - 1))
        ct = int(w[t % P])
        row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
    return row, cols
# get an absorbed state
row = random.getrandbits(300)
row, _ = evolve(row, 0, 2000)
t0 = 2000
_, ref = evolve(row, t0, 64, record=L)
broke = 0; first_breaks = []
for tr in range(trials):
    width = row.bit_length() + 10
    keep = row & ((1 << (k - 1)) - 1)      # positions 1..k-1 kept (bits 0..k-2)
    newrow = keep | (random.getrandbits(width) << (k - 1))
    _, cols = evolve(newrow, t0, horizon, record=L)
    # compare layer columns 1..L with reference periodic pattern (period 8P divides 64?)
    Q = 8 * P if 64 % (8 * P) == 0 else 64
    bad = None
    for i in range(horizon):
        if cols[i] != ref[i % 64]: bad = i; break
    if bad is not None: broke += 1; first_breaks.append(bad)
print(f"w={w} k={k}: layer (cols 1..{L}) broken in {broke}/{trials} trials; first-break times (sample): {sorted(first_breaks)[:10]}")
