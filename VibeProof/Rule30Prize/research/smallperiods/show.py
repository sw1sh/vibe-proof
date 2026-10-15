import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/smallperiods')
w = sys.argv[1]; width = int(sys.argv[2]); t0 = int(sys.argv[3]); t1 = int(sys.argv[4]); ncols = int(sys.argv[5])
random.seed(int(sys.argv[6]) if len(sys.argv)>6 else 1)
init = random.getrandbits(width) | (1 << (width-1))
row = init; W = width
for t in range(t1):
    if t >= t0:
        s = str(int(w[t % len(w)])) + '|' + ''.join('#' if (row >> i) & 1 else '.' for i in range(ncols))
        print('%5d %s' % (t, s))
    W += 1; mask = (1 << W) - 1
    leftn = ((row << 1) | int(w[t % len(w)])) & mask
    row = (leftn ^ (row | (row >> 1))) & mask
