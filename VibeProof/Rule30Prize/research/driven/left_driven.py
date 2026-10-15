# Left half of rule 30 (positions p = -1, -2, ...) driven by a given boundary column c(t) at p = 0.
# bit i <-> p = -(i+1).  new(p) = old(p-1) xor (old(p) or old(p+1)), old(0) = c(t).
import sys, itertools
def run_left(cfun, steps):
    row = 0; col = []   # column -1 history
    for t in range(steps):
        col.append(row & 1)
        W = t + 2
        mask = (1 << W) - 1
        right = ((row << 1) | cfun(t)) & mask      # bit i <- old(p+1): i-1, and i=0 <- c(t)
        left = row >> 1                            # bit i <- old(p-1): i+1
        row = (left ^ (row | right)) & mask
    return col
def run_right(cfun, steps):
    # right half p = 1, 2, ...: bit i <-> p = i+1; new(p) = old(p-1) xor (old(p) or old(p+1)), old(0) = c(t)
    row = 0; col = []
    for t in range(steps):
        col.append(row & 1)
        W = t + 2; mask = (1 << W) - 1
        leftn = ((row << 1) | cfun(t)) & mask     # old(p-1): bit i-1, i=0 <- c(t)
        rightn = row >> 1                          # old(p+1): bit i+1
        row = (leftn ^ (row | rightn)) & mask
    return col
def eventual_period(seq, maxP=4096):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
steps = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
# sanity: drive with the TRUE center column -> column -1 must equal the real rule 30 column -1
N = steps
row = 1 << N; center = []; colm1 = []; col1 = []
for t in range(N):
    center.append((row >> N) & 1); colm1.append((row >> (N - 1)) & 1); col1.append((row >> (N + 1)) & 1)
    row = (row << 1) ^ (row | (row >> 1))
print("sanity left :", run_left(lambda t: center[t], N) == colm1)
print("sanity right:", run_right(lambda t: center[t], N) == col1)
print("true column -1 eventual period:", eventual_period(colm1))
# periodic drivers: c(0) = 1 (the seed), then a periodic word w repeated
words = ['01', '10', '011', '001', '110', '0111', '0001', '0110', '00111', '01011', '0010111', '1101000']
for w in words:
    cf = lambda t, w=w: 1 if t == 0 else int(w[(t - 1) % len(w)])
    L = run_left(cf, steps); R = run_right(cf, steps)
    print(f"driver 1+({w})^*: left col -1 eventual period {eventual_period(L)} | right col 1 eventual period {eventual_period(R)}")
