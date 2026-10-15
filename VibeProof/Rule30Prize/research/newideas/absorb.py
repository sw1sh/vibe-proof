# Weak right-absorption test.
# Right half p >= 1 driven by c (column 0); bit i <-> p = i+1.
# Criterion (rigorous reduction): if c is eventually P-periodic and col_1 restricted to zeros of c is
# eventually periodic, then col_{-1}(t) = c(t+1) xor (c(t) or col_1(t)) is eventually periodic -> Jen.
import sys, random, itertools
def run_right(cvals, init=0, width_extra=0):
    row = init; col = []
    W = max(init.bit_length(), 1) + len(cvals) + 2 + width_extra
    mask = (1 << W) - 1
    for t, ct in enumerate(cvals):
        col.append(row & 1)
        leftn = ((row << 1) | ct) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return col
def masked_eventual_period(col, c, P, maxmult=64, tail_frac=0.5):
    # smallest Q = P*m such that col(t) == col(t+Q) for all t in second half with c(t) == 0
    n = len(col)
    start = int(n * tail_frac)
    for m in range(1, maxmult + 1):
        Q = P * m
        if start + Q >= n: break
        ok = True
        for t in range(start, n - Q):
            if c[t] == 0 and col[t] != col[t + Q]:
                ok = False; break
        if ok:
            # find transient: earliest T with property from T on
            T = start
            while T > 0 and (c[T - 1] == 1 or col[T - 1] == col[T - 1 + Q]): T -= 1
            return (T, Q)
    return None
def full_eventual_period(col, P, maxmult=64, tail_frac=0.5):
    return masked_eventual_period(col, [0] * len(col), P, maxmult, tail_frac)
def primitive_words(P):
    for bits in itertools.product('01', repeat=P):
        w = ''.join(bits)
        # canonical rotation & primitive
        if any(w == w[k:] + w[:k] for k in range(1, P) if P % k == 0) : continue
        if w != min(w[k:] + w[:k] for k in range(P)): continue
        yield w
if __name__ == '__main__':
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    Pmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    random.seed(1)
    for P in range(2, Pmax + 1):
        for w in primitive_words(P):
            res = []
            for trial in range(trials + 1):
                # trial 0: zero initial state with driver 1 then w^inf; others: random initial right state of width 200
                if trial == 0:
                    init = 0; pre = [1]
                else:
                    init = random.getrandbits(200); pre = [random.getrandbits(1) for _ in range(50)]
                c = pre + [int(w[(t) % P]) for t in range(steps)]
                col = run_right(c, init)
                cc = c[:len(col)]
                mp = masked_eventual_period(col, cc, P)
                res.append('A' if mp else '-')
            print(P, w, ''.join(res), flush=True)
