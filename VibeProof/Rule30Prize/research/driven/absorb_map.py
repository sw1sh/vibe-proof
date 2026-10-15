import random, itertools
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
def necklaces(n):
    seen = set(); out = []
    for bits in itertools.product('01', repeat=n):
        w = ''.join(bits)
        rots = [w[i:] + w[:i] for i in range(n)]
        m = min(rots)
        if m in seen: continue
        seen.add(m)
        if any(w == w[:d] * (n // d) for d in range(1, n) if n % d == 0): continue  # not primitive
        out.append(m)
    return out
random.seed(7)
steps = 3000
summary = {}
for n in range(2, 9):
    absorbing = []; mixed = []; chaotic = []
    for w in necklaces(n):
        res = []
        for trial in range(3):
            W0 = random.choice([16, 256, 1500])
            init = random.getrandbits(W0) | (1 << (W0 - 1))
            ep = eventual_period(run_right(w, init, W0, steps), maxP=600)
            res.append(ep is not None and ep[0] < 1200)
        (absorbing if all(res) else chaotic if not any(res) else mixed).append(w)
    print(f"length {n}: absorbing {absorbing} | mixed {mixed} | chaotic {len(chaotic)} words")
