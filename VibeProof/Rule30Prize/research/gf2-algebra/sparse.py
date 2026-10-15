# Right half (positions 1..) driven by c = w^infinity at position 0, from random finite initial states.
# Report the eventual period of column 1 (None = not periodic within the window).
import random, sys
def run_right(w, init, steps):
    row = init; col = []; P = len(w)
    for t in range(steps):
        col.append(row & 1)
        W = row.bit_length() + 3; mask = (1 << W) - 1
        c = w[t % P]
        leftn = ((row << 1) | c) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return col
def eventual(seq, maxP=2048):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
rng = random.Random(7)
steps = int(sys.argv[1])
for w in ['001', '0001', '00001', '000001', '0000001', '0111', '0110', '011', '01', '00011', '00101']:
    res = []
    for trial in range(6):
        init = rng.getrandbits(rng.choice([20, 100, 300]))
        res.append(eventual(run_right([int(ch) for ch in w], init, steps)))
    print(w, res)
