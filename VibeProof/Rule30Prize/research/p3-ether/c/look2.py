# Right half driven by c = 1 then w^inf.  Report, for times t, the first column where row(t) != row(t+P) (P = 21),
# and the extent of the stripe region.
import sys
w = sys.argv[1]; steps = int(sys.argv[2]); P = int(sys.argv[3])
row = 0
def cf(t): return 1 if t == 0 else int(w[(t - 1) % len(w)])
rows = []
for t in range(steps):
    c = cf(t); full = (row << 1) | c
    rows.append(full)
    n = t + 3; mask = (1 << n) - 1
    row = ((full & mask) ^ (((full >> 1) & mask) | ((full >> 2) & mask))) & mask
for t in range(200, steps - P, (steps - P - 200) // 25):
    d = rows[t] ^ rows[t + P]
    fd = (d & -d).bit_length() - 1 if d else -1
    print(f"t={t:6d} first column where row(t) != row(t+{P}): {fd}")
