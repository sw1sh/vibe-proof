# Independent check: right half driven by w from random configs; verify column-1 values at given phases after time t0
import sys, random
w = sys.argv[1]; t0 = int(sys.argv[2]); steps = int(sys.argv[3]); trials = int(sys.argv[4]); W0 = int(sys.argv[5])
p = len(w)
viol = 0; seen = {}
for tr in range(trials):
    random.seed(tr * 7919 + 13)
    row = random.getrandbits(W0) | (1 << (W0 - 1)) if W0 > 0 else 0
    W = W0
    for t in range(steps):
        b = row & 1
        if t >= t0:
            seen.setdefault(t % p, set()).add(b)
        W += 1; mask = (1 << W) - 1
        row = ((((row << 1) | int(w[t % p])) & mask) ^ (row | (row >> 1))) & mask
print(w, {ph: sorted(v) for ph, v in sorted(seen.items())})
