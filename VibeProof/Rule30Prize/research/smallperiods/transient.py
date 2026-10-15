import sys, random
w = sys.argv[1]; width = int(sys.argv[2]); steps = int(sys.argv[3]); Q = int(sys.argv[4]); seeds = int(sys.argv[5]); k = int(sys.argv[6])
p = len(w)
res = []
for seed in range(seeds):
    random.seed(1000 + seed)
    init = random.getrandbits(width) | (1 << (width - 1))
    row = init; W = width; rows = []
    for t in range(steps):
        rows.append(row & ((1 << k) - 1))
        W += 1; mask = (1 << W) - 1
        leftn = ((row << 1) | int(w[t % p])) & mask
        row = (leftn ^ (row | (row >> 1))) & mask
    # transient: smallest T such that rows[t] == rows[t+Q] for all t in [T, steps-Q)
    T = steps - Q
    while T > 0 and rows[T-1] == rows[T-1+Q]: T -= 1
    res.append(T if T < steps - 4*Q else None)
ok = [r for r in res if r is not None]
print(w, 'width', width, 'trapped', len(ok), '/', len(res), 'transients sorted', sorted(ok)[:5], '...', sorted(ok)[-5:], 'mean', sum(ok)/max(1,len(ok)))
