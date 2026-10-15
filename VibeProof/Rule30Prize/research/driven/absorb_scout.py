# Right half driven by a periodic word w from RANDOM finite right-half states (with the cone's right edge:
# a one at the rightmost position that keeps moving right). Is column 1 eventually periodic?
import random, sys
def run_right(w, init_bits, W0, steps):
    row = init_bits; width = W0; col = []
    for t in range(steps):
        col.append(row & 1)
        width += 1; mask = (1 << width) - 1
        leftn = ((row << 1) | int(w[t % len(w)])) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return col
def eventual_period(seq, maxP=2048):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
random.seed(1)
steps = 4000
for w in ['0001', '0110', '0111', '001', '01', '011', '0011', '00011', '000111', '0000001']:
    res = []
    for trial in range(6):
        W0 = random.choice([8, 64, 512, 2000])
        init = random.getrandbits(W0) | (1 << (W0 - 1))   # rightmost cell black (cone edge)
        res.append(eventual_period(run_right(w, init, W0, steps)))
    print(w, res)
