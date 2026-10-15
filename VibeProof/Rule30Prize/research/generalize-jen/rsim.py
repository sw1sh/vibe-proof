# Right half of rule 30 driven at p=0 by c(t); bit i of row <-> position p=i+1.
# Compare eventual periodicity of d = column 1 and e = c OR d.
import sys, random

def true_rows(Tmax):
    """yield (t, right-half row at time t as int, center c(t)) for the true rule-30 pattern"""
    N = Tmax + 2
    row = 1 << N
    for t in range(Tmax + 1):
        c = (row >> N) & 1
        rh = row >> (N + 1)         # positions >= 1
        yield t, rh, c
        row = (row << 1) ^ (row | (row >> 1))

def run(word, row, steps):
    wb = [int(ch) for ch in word]; P = len(wb)
    d = bytearray(steps); col2 = bytearray(steps); cc = bytearray(steps)
    for t in range(steps):
        c = wb[t % P]
        cc[t] = c; d[t] = row & 1; col2[t] = (row >> 1) & 1
        row = ((row << 1) | c) ^ (row | (row >> 1))
    return cc, d, col2

def eventual_period(seq, maxP=None):
    n = len(seq)
    if maxP is None: maxP = n // 4
    h = n // 2
    for P in range(1, maxP + 1):
        if seq[h:n-P] == seq[h+P:n]:
            T = h
            while T > 0 and seq[T-1] == seq[T-1+P]: T -= 1
            return (T, P)
    return None

if __name__ == '__main__':
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    words = sys.argv[2].split(',') if len(sys.argv) > 2 else ['01','001','011','0001','0011','0111','0110','00111','01011']
    Ts = [5, 20, 77, 200, 500]
    rows = {}
    for t, rh, c in true_rows(max(Ts)):
        if t in Ts: rows[t] = rh
    for w in words:
        out = []
        for T in Ts:
            cc, d, _ = run(w, rows[T], steps)
            e = bytes(a | b for a, b in zip(cc, d))
            out.append((T, eventual_period(bytes(d)), eventual_period(e)))
        print(w, ' '.join(f"T{T}:d{pd}e{pe}" for T, pd, pe in out), flush=True)
