# Reachable strip-state sets under a constant input (run of 1s or 0s), strip width b, free column b+1.
import sys
def step_set(S, cval, b):
    out = set()
    for s in S:
        bit = lambda p: cval if p == 0 else (s >> (p - 1)) & 1
        base = 0
        for p in range(1, b):
            base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
        if bit(b): out.add(base | ((1 ^ bit(b - 1)) << (b - 1)))
        else: out.add(base); out.add(base | (1 << (b - 1)))
    return out
b = int(sys.argv[1]); cval = int(sys.argv[2])
S = set(range(1 << b))
for m in range(1, 40):
    S = step_set(S, cval, b)
    c1 = set(s & 1 for s in S); c12 = set((s & 1) | ((s >> 1) & 1) for s in S)
    print(m, len(S), "col1 values:", sorted(c1), "col1|col2 values:", sorted(c12))
    if m > 3 and len(S) == prev: break
    prev = len(S)
