import sys, random
w = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3]); ncols = int(sys.argv[4])
random.seed(seed)
row = random.getrandbits(200)
P = len(w)
W = 200 + steps + 4; mask = (1 << W) - 1
for t in range(steps):
    ct = int(w[t % P])
    if t >= steps - 3 * P:
        print(f"{t:5d} {ct} | " + ''.join('#' if (row >> i) & 1 else '.' for i in range(ncols)))
    row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
