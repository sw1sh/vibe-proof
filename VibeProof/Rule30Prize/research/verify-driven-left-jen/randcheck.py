# Random sanity check of the claim: left-finite nonzero initial left half, eventually periodic driver
# (random transient + random word) => columns -1..-K show no eventual period in a long window.
# Also checks the edge lemma (leftmost black moves left exactly one cell per step).
import random, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
def run(xbits, xlen, cfun, steps, K):
    # bit i <-> p = -(i+1); row holds the left half
    row = xbits; cols = [[] for _ in range(K)]
    q0 = None
    for t in range(steps):
        for k in range(K): cols[k].append((row >> k) & 1)
        # edge: highest set bit index = -(p)-1 of leftmost black
        lead = row.bit_length() - 1
        if q0 is None: q0 = lead
        assert xbits == 0 or lead == q0 + t, (t, lead, q0)
        W = xlen + t + 3; mask = (1 << W) - 1
        right = ((row << 1) | cfun(t)) & mask
        left = row >> 1
        row = (left ^ (row | right)) & mask
    return cols
def eventual_period(seq, maxP):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
bad = 0; trials = 0
for trial in range(40):
    xlen = random.randint(1, 12)
    xbits = random.getrandbits(xlen) | (1 << (xlen - 1))   # nonzero, leftmost black at p=-xlen
    tr = [random.randint(0, 1) for _ in range(random.randint(0, 20))]
    w = [random.randint(0, 1) for _ in range(random.randint(1, 8))]
    cf = lambda t, tr=tr, w=w: tr[t] if t < len(tr) else w[(t - len(tr)) % len(w)]
    cols = run(xbits, xlen, cf, 2400, 6)
    for k, col in enumerate(cols):
        trials += 1
        ep = eventual_period(col, 400)
        if ep is not None:
            bad += 1; print("apparent period", trial, k + 1, ep, xlen, tr, w)
print("columns checked:", trials, "apparent periods:", bad)
# necessity of hypotheses: all-white start with c = 0 -> column -1 constant
cols = run(0, 1, lambda t: 0, 200, 2)
print("all-white, c=0: column -1 period", eventual_period(cols[0], 10))
