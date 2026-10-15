import random, sys
def col1(w, init, W0, steps):
    row = init; width = W0; out = bytearray(steps)
    L = len(w); wb = [int(ch) for ch in w]
    for t in range(steps):
        out[t] = row & 1
        width += 1; mask = (1 << width) - 1
        row = ((((row << 1) | wb[t % L]) & mask) ^ (row | (row >> 1))) & mask
    return out
def tail_periodic_from(seq, P):
    n = len(seq); T = n - P
    while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
    return T   # seq is P-periodic on [T, n)
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 11)
w = sys.argv[1]; steps = 12000
res = []
for trial in range(10):
    W0 = random.choice([16, 100, 1000, 4000])
    init = random.getrandbits(W0) | (1 << (W0 - 1))
    s = col1(w, init, W0, steps)
    res.append(tail_periodic_from(s, len(w)) if len(w) else None)
print(w, "periodic-from times (n=%d):" % steps, res)
