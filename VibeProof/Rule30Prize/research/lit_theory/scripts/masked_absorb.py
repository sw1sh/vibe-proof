# Refinement of the 'absorbing word' test via the NKS-10.10 / "scattered cells" observation:
# cell(t,-1) = c(t+1) XOR (c(t) OR cell(t,1)) only uses cell(t,1) when c(t)=0.
# So if c is eventually periodic and b(t) := cell(t,1) AND NOT c(t) is eventually periodic, then
# column -1 is eventually periodic too, contradicting Jen (two adjacent periodic columns).
# Test: right half driven by w^inf from random finite right-half states (cone edge at the right),
# is column 1 eventually periodic? is the masked sequence b eventually periodic?
import random, sys
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
def eventual_period(seq, maxP=1024):
    n = len(seq)
    for P in range(1, maxP + 1):
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return (T, P)
    return None
random.seed(7)
steps = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
words = ['01','10','011','110','001','0111','0001','0110','00111','01011','0010111','1101000','0011','00011','000111','0101','1011','0100']
for w in words:
    full = []; masked = []
    for trial in range(4):
        W0 = random.choice([8, 64, 400])
        init = random.getrandbits(W0) | (1 << (W0 - 1))
        col, b = run_right(w, init, W0, steps)
        full.append(eventual_period(col)); masked.append(eventual_period(b))
    print(w.ljust(8), 'col1:', ['ap' if r is None else 'P%d' % r[1] for r in full], ' masked b:', ['ap' if r is None else 'P%d' % r[1] for r in masked])
