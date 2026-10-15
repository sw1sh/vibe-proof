# Independent check of smallperiods C8: under driver (001)^inf, adversarial right strip (cols 1..W, col W+1 free),
# reachable sets from all states; check that column 1 at phase 0 (time right after a center 1) is eventually forced white.
import sys
def step(s, left, x, W):
    # s: bit i = column i+1. new col p = col p-1 xor (col p or col p+1)
    full = left | (s << 1) | (x << (W + 1))      # bit 0 = col 0, bit i = col i, bit W+1 = col W+1
    new = 0
    for p in range(1, W + 1):
        a = (full >> (p - 1)) & 1; b = (full >> p) & 1; c = (full >> (p + 1)) & 1
        new |= (a ^ (b | c)) << (p - 1)
    return new
def run(word, W, maxsteps=200):
    P = len(word)
    R = set(range(1 << W))   # time 0 at phase 0
    hist = [R]
    for t in range(maxsteps):
        left = word[t % P]
        R = {step(s, left, x, W) for s in R for x in (0, 1)}
        hist.append(R)
        n = len(hist) - 1
        if n >= P and hist[n] == hist[n - P]:
            # repeating sets; report column-1 values at each phase
            out = []
            for ph in range(P):
                Rs = hist[n - P + ((ph - (n - P)) % P)]
                vals = {s & 1 for s in Rs}
                out.append(''.join(sorted(str(v) for v in vals)))
            return n, [len(hist[n - P + i]) for i in range(P)], out
    return None
word = [int(ch) for ch in sys.argv[1]]
W = int(sys.argv[2])
print(sys.argv[1], W, run(word, W))
