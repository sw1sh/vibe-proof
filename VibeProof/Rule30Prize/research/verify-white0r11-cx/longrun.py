# Long bit-packed simulation of the right half driven by (0^r 11)^inf; per-period column-1 words;
# test whether the per-period sequence becomes periodic in the tail.
import sys, random, time

def run(r, R, periods, phase0=True):
    Q = r + 2
    w = [0] * r + [1, 1]
    words = []
    for k in range(periods):
        word = 0
        for i in range(Q):
            word = (word << 1) | (R & 1)
            d = w[i]
            R = ((R << 1) | d) ^ (R | (R >> 1))
        words.append(word)
    return words

def tail_period(seq, maxp):
    n = len(seq)
    half = n // 2
    for p in range(1, maxp + 1):
        if all(seq[i] == seq[i + p] for i in range(half, n - p)):
            return p
    return None

def true_right_half(T):
    # rule 30 from single cell as bit-packed integer over columns -T..T, return columns >= 1 at time T
    # represent full row with offset: bit (p + T + 1) ... simpler: simulate both halves as one int with offset
    off = T + 2
    row = 1 << off
    for t in range(T):
        row = (row << 1) ^ (row | (row >> 1))  # careful: (row<<1) gives left neighbour at bit p
    # after T steps, bit (off + p) ... check orientation below
    return row, off

rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
r = int(sys.argv[1])
periods = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
t0 = time.time()
res = []
for trial in range(int(sys.argv[4]) if len(sys.argv) > 4 else 12):
    kind = trial % 3
    if kind == 0:
        n = rng.randint(1, 60); R = rng.getrandbits(n) | 1 << (n - 1)
    elif kind == 1:
        n = rng.randint(100, 300); R = rng.getrandbits(n) | 1 << (n - 1)
    else:
        R = 1 << rng.randint(0, 40)
    words = run(r, R, periods)
    p = tail_period(words, periods // 4)
    distinct_tail = len(set(words[periods // 2:]))
    res.append((kind, p, distinct_tail))
    print(f"r={r} trial={trial} kind={kind} tail period (in periods) = {p}  distinct words in tail = {distinct_tail}  t={time.time()-t0:.1f}s", flush=True)
    if time.time() - t0 > 45: break
