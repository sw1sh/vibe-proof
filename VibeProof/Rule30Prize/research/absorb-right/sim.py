# Right half of rule 30 (cells p >= 1) driven at p = 0 by c(t) = w[(phase+t) mod |w|].
# bit i of row <-> p = i+1. new(p) = old(p-1) xor (old(p) or old(p+1)), old(0) = c(t).
import random, sys

def run(w, phase, row, steps):
    wb = [int(ch) for ch in w]; L = len(wb)
    col = bytearray(steps)
    for t in range(steps):
        col[t] = row & 1
        c = wb[(phase + t) % L]
        row = ((row << 1) | c) ^ (row | (row >> 1))
    return col, row

def eventual_period(seq, maxP=None):
    n = len(seq)
    if maxP is None: maxP = n // 4
    best = None
    for P in range(1, maxP + 1):
        # check last half periodic with period P
        ok = True
        for t in range(n // 2, n - P):
            if seq[t] != seq[t + P]:
                ok = False; break
        if ok:
            T = n // 2
            while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
            return (T, P)
    return None

def lyndon_words(n):
    # all binary Lyndon words of length exactly n
    res = []
    for x in range(2**n):
        s = format(x, '0%db' % n)
        if all(s < s[i:] + s[:i] for i in range(1, n)):
            res.append(s)
    return res
