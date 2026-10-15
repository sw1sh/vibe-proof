import random, sys
def evolve_rows(w, init, W0, steps):
    row = init; width = W0; rows = []
    L = len(w); wb = [int(ch) for ch in w]
    for t in range(steps):
        rows.append(row)
        width += 1; mask = (1 << width) - 1
        row = ((((row << 1) | wb[t % L]) & mask) ^ (row | (row >> 1))) & mask
    return rows
w = sys.argv[1]; P = len(w)
random.seed(5)
for trial in range(3):
    W0 = random.choice([200, 1500]); init = random.getrandbits(W0) | (1 << (W0 - 1))
    rows = evolve_rows(w, init, W0, 6000)
    lo, hi = 4000, 6000
    line = []
    for k in range(40):   # bit k = column k+1
        forced = []
        for ph in range(P):
            vals = {(rows[t] >> k) & 1 for t in range(lo, hi) if t % P == ph}
            forced.append(str(vals.pop()) if len(vals) == 1 else '*')
        line.append(''.join(forced))
    print(f"{w} trial {trial}: per column (phase 0..{P-1}; * = varies):", ' '.join(line))
