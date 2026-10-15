import random
def run_right(w, init_bits, W0, steps):
    row = init_bits; width = W0; col = []; b = []
    for t in range(steps):
        c = int(w[t % len(w)])
        col.append(row & 1); b.append((row & 1) & (1 - c))
        width += 1; mask = (1 << width) - 1
        leftn = ((row << 1) | c) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return col, b
def eventual_period(seq, maxP=2048):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
random.seed(11)
for w in ['001', '01']:
    out = []
    for trial in range(3):
        W0 = random.choice([8, 64, 400])
        init = random.getrandbits(W0) | (1 << (W0 - 1))
        col, b = run_right(w, init, W0, 9000)
        out.append((W0, eventual_period(col), eventual_period(b)))
    # zero-ish initial state: single right-edge cell
    col, b = run_right(w, 1, 1, 9000)
    out.append(('edge-only', eventual_period(col), eventual_period(b)))
    print(w, out)
