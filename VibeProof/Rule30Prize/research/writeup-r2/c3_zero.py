#!/usr/bin/env python3
"""C3(w) sanity: driven left half (rule 30 on p <= -1, column 0 = c'_w periodic), bit k-1 of an int = depth k.
Reports whether column -1 matches P_w at the fixed phases on a late window, for the zero start and small starts."""
import itertools
CP = {'0001': '0000', '0011': '0010', '0111': '0110'}
PW = {'0001': '0*01', '0011': '*001', '0111': '*001'}
def col_m1(x, cprime, T):
    out = []
    for t in range(T):
        out.append(x & 1)
        c = int(cprime[t % 4])
        # new depth k = old depth k+1 xor (old depth k or old depth k-1); depth 0 is the boundary c
        x = (x >> 1) ^ (x | ((x << 1) | c))
    return out
def ok(col, pw, t0):
    return all(pw[t % 4] == '*' or int(pw[t % 4]) == col[t] for t in range(t0, len(col)))
for w in ('0001', '0011', '0111'):
    z = col_m1(0, CP[w], 2000)
    bad = [t for t in range(2000) if PW[w][t % 4] != '*' and int(PW[w][t % 4]) != z[t]]
    print(f"w={w}: zero start: violations of P_w at {len(bad)} of 2000 steps, last at {bad[-1] if bad else None}")
    cnt = tot = 0
    for W in range(1, 15):
        for b in range(1 << (W - 1)):
            x = b | (1 << (W - 1)); tot += 1
            if ok(col_m1(x, CP[w], 300), PW[w], 150): cnt += 1
    print(f"   nonzero starts with leftmost black at depth W <= 14: {cnt} of {tot} match P_w on [150, 300)")
