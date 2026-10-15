import sys, random
def rows_right(cvals, init):
    row = init; rows = []
    W = max(init.bit_length(), 1) + len(cvals) + 2
    mask = (1 << W) - 1
    for t, ct in enumerate(cvals):
        rows.append(row)
        row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
    return rows
w = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3]); initw = int(sys.argv[4]); k = int(sys.argv[5])
random.seed(seed)
init = random.getrandbits(initw)
P = len(w)
c = [int(w[t % P]) for t in range(steps)]
rows = rows_right(c, init)
a = steps - 64
print("t%8 c | cols 1..k+4 (| marks after col k)")
for t in range(a, a + 40):
    s = ''.join('#' if (rows[t] >> i) & 1 else '.' for i in range(k)) + '|' + ''.join('#' if (rows[t] >> i) & 1 else '.' for i in range(k, k + 6))
    print(t % 8, c[t], s)
