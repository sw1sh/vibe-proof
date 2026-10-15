# Right half (p>=1) driven by boundary c at p=0, from given initial right-half config.
# bit i <-> p = i+1. new(p) = old(p-1) xor (old(p) or old(p+1)), old(0) = c(t).
import sys, random
def run_right(init, width, cfun, steps, cols=(1,)):
    row = init
    out = {k: [] for k in cols}
    W = width
    for t in range(steps):
        for k in cols: out[k].append((row >> (k-1)) & 1)
        W += 1
        mask = (1 << W) - 1
        leftn = ((row << 1) | cfun(t)) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return out, row
def eventual_period(seq, maxP=4096):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
if __name__ == '__main__':
    w = sys.argv[1]; steps = int(sys.argv[2]); trials = int(sys.argv[3]); width = int(sys.argv[4])
    random.seed(int(sys.argv[5]) if len(sys.argv)>5 else 1)
    res = {}
    for tr in range(trials):
        init = random.getrandbits(width) | (1 << (width-1))
        cf = lambda t: int(w[t % len(w)])
        out, _ = run_right(init, width, cf, steps)
        ep = eventual_period(out[1])
        key = None if ep is None else ep[1]
        res.setdefault(key, []).append(ep[0] if ep else None)
    for k in res: print(w, 'period', k, 'count', len(res[k]), 'max transient', max([x for x in res[k] if x is not None], default=None))
