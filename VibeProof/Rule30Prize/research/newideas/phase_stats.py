# Per-(column, phase) frequency of 1s in the right half driven by w^inf after transient.
import sys, random
w = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3]); initw = int(sys.argv[4]); ncol = int(sys.argv[5]); Q = int(sys.argv[6])
random.seed(seed)
row = random.getrandbits(initw)
P = len(w)
W = initw + steps + 4; mask = (1 << W) - 1
cnt = [[0] * Q for _ in range(ncol)]; tot = [0] * Q
for t in range(steps):
    ct = int(w[t % P])
    if t >= steps // 2:
        ph = t % Q; tot[ph] += 1
        for p in range(ncol):
            cnt[p][ph] += (row >> p) & 1
    row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
for p in range(ncol):
    s = ''
    for ph in range(Q):
        f = cnt[p][ph] / tot[ph]
        s += '1' if f == 1 else ('0' if f == 0 else ('h' if 0.3 < f < 0.7 else ('l' if f <= 0.3 else 'H')))
    print(f"col {p+1:3d}: {s}")
