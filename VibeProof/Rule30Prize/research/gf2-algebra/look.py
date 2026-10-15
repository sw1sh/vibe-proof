import random, sys
w = [int(ch) for ch in sys.argv[1]]; P = len(w)
rng = random.Random(int(sys.argv[2]))
row = rng.getrandbits(200)  # bit i <-> position i+1
hist = []
for t in range(3000):
    hist.append(row)
    W = row.bit_length() + 3; mask = (1 << W) - 1
    c = w[t % P]
    row = ((((row << 1) | c) & mask) ^ (row | (row >> 1))) & mask
# print columns 0..40 for the last 3 periods-worth of rows, aligned
for t in range(3000 - 4 * P, 3000):
    r = hist[t]
    s = str(w[t % P]) + '|' + ''.join('#' if (r >> i) & 1 else '.' for i in range(60))
    print("%5d %s" % (t, s))
