import sys, random
w = sys.argv[1]; width = int(sys.argv[2]); steps = int(sys.argv[3]); seed = int(sys.argv[4]); blk = int(sys.argv[5])
random.seed(seed)
init = random.getrandbits(width) | (1 << (width - 1))
row = init; W = width; col = []
p = len(w)
for t in range(steps):
    col.append(row & 1)
    W += 1; mask = (1 << W) - 1
    leftn = ((row << 1) | int(w[t % p])) & mask
    row = (leftn ^ (row | (row >> 1))) & mask
s = ''.join(map(str, col))
for i in range(0, min(len(s), 2000), 100):
    print(' '.join(s[j:j+blk] for j in range(i, i+100, blk)))
