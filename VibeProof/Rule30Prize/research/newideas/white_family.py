# Mechanism for 0^k 1: start from the white-run attractor A (long white run), apply one black step,
# then white steps; print possible col_1 values at each step, and whether we are back inside A.
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
b = int(sys.argv[1]); rounds = int(sys.argv[2]); k = int(sys.argv[3])
S = set(range(1 << b))
for _ in range(60): S = step_set(S, 0, b)
A = S
print("white attractor size", len(A), "col1 values", sorted(set(s & 1 for s in A)))
S = set(range(1 << b))
for r in range(rounds):
    vals = []
    for j in range(k):
        vals.append(''.join(map(str, sorted(set(s & 1 for s in S)))))
        S = step_set(S, 0, b)
    print(f"round {r}: col1 sets during white run of length {k}: {' '.join(vals)}; |S|={len(S)}")
    S = step_set(S, 1, b)
