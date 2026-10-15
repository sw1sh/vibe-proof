import sys, random
def run_right_rows(cvals, init=0):
    row = init; rows = []
    W = max(init.bit_length(), 1) + len(cvals) + 2
    mask = (1 << W) - 1
    for t, ct in enumerate(cvals):
        rows.append(row)
        leftn = ((row << 1) | ct) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return rows
w = sys.argv[1]; steps = int(sys.argv[2]); ncols = int(sys.argv[3]); seed = int(sys.argv[4])
random.seed(seed)
init = random.getrandbits(300) if seed else 0
P = len(w)
c = [int(w[t % P]) for t in range(steps)]
rows = run_right_rows(c, init)
for t in range(steps - 4 * P * 3, steps):
    r = rows[t]
    print(f"{t:6d} {c[t]} | " + ''.join('#' if (r >> i) & 1 else '.' for i in range(ncols)))
