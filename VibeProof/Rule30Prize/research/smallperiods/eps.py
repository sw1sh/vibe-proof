import sys, random
w = sys.argv[1]; width = int(sys.argv[2]); t0 = int(sys.argv[3]); nshow = int(sys.argv[4]); ncols = int(sys.argv[5]); seed = int(sys.argv[6]); P = int(sys.argv[7])
random.seed(seed)
init = random.getrandbits(width) | (1 << (width-1))
rows = []
row = init; W = width
for t in range(t0 + nshow + P + 1):
    rows.append(row)
    W += 1; mask = (1 << W) - 1
    leftn = ((row << 1) | int(w[t % len(w)])) & mask
    row = (leftn ^ (row | (row >> 1))) & mask
for t in range(t0, t0 + nshow):
    r = rows[t]; e = rows[t] ^ rows[t+P]
    s = ''.join(('X' if (e>>i)&1 else '#') if (r>>i)&1 else ('o' if (e>>i)&1 else '.') for i in range(ncols))
    print('%5d %s|%s' % (t, w[t%len(w)], s))
