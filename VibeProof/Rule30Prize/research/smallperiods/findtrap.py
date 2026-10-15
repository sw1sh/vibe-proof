# Find the trap orbit for driver w: columns 1..k periodic with period Q (multiple of len(w)).
import sys, random
w = sys.argv[1]; width = int(sys.argv[2]); steps = int(sys.argv[3]); Q = int(sys.argv[4]); seeds = int(sys.argv[5])
p = len(w)
orbits = {}
for seed in range(seeds):
    random.seed(seed)
    init = random.getrandbits(width) | (1 << (width - 1))
    row = init; W = width; rows = []
    for t in range(steps):
        rows.append(row)
        W += 1; mask = (1 << W) - 1
        leftn = ((row << 1) | int(w[t % p])) & mask
        row = (leftn ^ (row | (row >> 1))) & mask
    # largest k such that columns 1..k are periodic with period Q over the last half
    half = steps // 2
    k = 0
    while True:
        bit = k
        ok = all(((rows[t] >> bit) & 1) == ((rows[t + Q] >> bit) & 1) for t in range(half, steps - Q))
        if not ok: break
        k += 1
        if k > 60: break
    # record orbit: for phase ph (t mod Q), the pattern of columns 1..k
    t0 = half - (half % Q)
    orb = tuple(''.join(str((rows[t0 + ph] >> i) & 1) for i in range(k)) for ph in range(Q))
    orbits.setdefault((k, orb), []).append(seed)
for (k, orb), ss in orbits.items():
    print('k =', k, 'seeds', len(ss))
    for ph in range(Q): print('  t%%%d=%d c=%s cols1..k=%s' % (Q, ph, w[ph % p], orb[ph]))
