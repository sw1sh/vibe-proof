# Independent simulation of the right half (columns >= 1) of rule 30 driven at column 0 by w^inf
# (w = 0^r 11, phase 0 = start of the white run).  Row as a Python int: bit i = column i+1.
# Checks the case analysis l -> l' and eventual periodicity of column 1.
import random
def step(row, d):
    return ((row << 1) | d) ^ (row | (row >> 1))
def first_black(row):
    return (row & -row).bit_length() - 1  # index of lowest set bit = l
def predicted(l, r):
    if l <= r - 8: return 'lock'
    if l <= r: return 'le1'
    z = l - r
    return {1: 1, 2: 'z2', 3: 2}.get(z, 1)
def run(r, M, periods, rnd):
    w = [0] * r + [1, 1]; Q = r + 2
    row = rnd.getrandbits(M) | (1 << M)
    ls = []; col1 = []; bad = []
    for k in range(periods):
        ls.append(first_black(row))
        for j in range(Q):
            col1.append(row & 1)
            row = step(row, w[j])
    for k in range(len(ls) - 1):
        l, l2 = ls[k], ls[k + 1]; p = predicted(l, r)
        ok = (p == 'lock' and l2 == 0) or (p == 'le1' and l2 <= 1) or p == 'z2' or p == l2
        if not ok: bad.append((k, l, l2, p))
    return ls, col1, bad
def per(seq, Q, tail):
    s = seq[-tail:]
    return all(s[i] == s[i + Q] for i in range(len(s) - Q))
if __name__ == '__main__':
    rnd = random.Random(12345)
    for r in [6, 7, 8, 9, 10, 11, 12, 15, 20]:
        Q = r + 2; nbad = 0; nper = 0; nper2 = 0; trials = 0; z2all = 0
        for trial in range(400):
            M = [3, 12, 40, 120][trial % 4]
            ls, col1, bad = run(r, M, 150, rnd)
            trials += 1; nbad += len(bad)
            if per(col1, Q, 60 * Q): nper += 1
            if per(col1, 2 * Q, 60 * Q): nper2 += 1
            if all(l == r + 2 for l in ls[-50:]): z2all += 1
        print(f"r={r}: trials={trials}, case-analysis violations={nbad}, col1 eventually per Q: {nper}, per 2Q: {nper2}, z2-forever tails: {z2all}")
