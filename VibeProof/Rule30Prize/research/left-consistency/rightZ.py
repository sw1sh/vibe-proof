# Right half driven by c = 1 then w^inf (as in the brief's experiment): is column 1 restricted to
# Z = {t : c(t) = 0} eventually periodic (with period a multiple of |w|) even when column 1 itself is not?
import sys
def run_right(cfun, steps):
    row = 0; col = []
    for t in range(steps):
        col.append(row & 1)
        W = t + 2; mask = (1 << W) - 1
        leftn = ((row << 1) | cfun(t)) & mask
        rightn = row >> 1
        row = (leftn ^ (row | rightn)) & mask
    return col
def eventual_period_on(seq, idx_ok, P0, maxmult=200):
    n = len(seq)
    for m in range(1, maxmult + 1):
        P = m * P0
        # find smallest T such that for all t >= T in Z with t+P < n: seq[t] == seq[t+P]
        bad = [t for t in range(n - P) if idx_ok(t) and seq[t] != seq[t + P]]
        T = (bad[-1] + 1) if bad else 0
        if T <= n // 2: return (T, P)
    return None
steps = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
words = sys.argv[2:] if len(sys.argv) > 2 else ['01', '10', '011', '110', '101', '001', '0111', '0001', '0110', '00111', '01011', '0010111', '1101000']
for w in words:
    cf = lambda t, w=w: 1 if t == 0 else int(w[(t - 1) % len(w)])
    R = run_right(cf, steps)
    full = eventual_period_on(R, lambda t: True, len(w))
    onZ = eventual_period_on(R, lambda t, cf=cf: cf(t) == 0, len(w))
    print(f"w={w}: col1 eventual period {full} | col1 restricted to c=0 times: {onZ}")
