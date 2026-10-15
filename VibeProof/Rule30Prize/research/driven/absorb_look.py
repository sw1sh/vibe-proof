import random
def evolve(w, init, W0, steps):
    row = init; width = W0; rows = []
    for t in range(steps):
        rows.append(row)
        width += 1; mask = (1 << width) - 1
        row = ((((row << 1) | int(w[t % len(w)])) & mask) ^ (row | (row >> 1))) & mask
    return rows
random.seed(3)
for w in ['0001', '0011', '0111', '01111']:
    W0 = 300; init = random.getrandbits(W0) | (1 << (W0 - 1))
    rows = evolve(w, init, W0, 1200)
    print(f"driver {w}: columns 1..24 (left = column 1), last {2*len(w)} rows, time t shown with c(t)")
    for t in range(1200 - 2 * len(w), 1200):
        r = rows[t]
        print(f"  t%{len(w)}={t%len(w)} c={w[t%len(w)]} |", ''.join('#' if (r >> i) & 1 else '.' for i in range(24)))
    # how far right does the periodic region extend? find largest k with columns 1..k periodic (period |w|) over last 400 rows
    P = len(w); k = 0
    while k < 200 and all(((rows[t] >> k) & 1) == ((rows[t - P] >> k) & 1) for t in range(800, 1200)): k += 1
    print(f"  columns 1..{k} are {P}-periodic over t in [800,1200)")
