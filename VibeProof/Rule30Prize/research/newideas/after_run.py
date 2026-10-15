# After a long black run of column 0, the strip (width b, free column b+1) lies in R_inf (black-run attractor).
# Then feed an arbitrary word (zeros and ones) and record the set of possible col_1 values at each step.
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
b = int(sys.argv[1]); runlen = int(sys.argv[2]); word = sys.argv[3]
S = set(range(1 << b))
for _ in range(runlen): S = step_set(S, 1, b)
print("after", runlen, "black steps:", len(S), "states")
line = ''
for ch in word:
    vals = sorted(set(s & 1 for s in S))
    line += f"c={ch}:col1{vals} "
    S = step_set(S, int(ch), b)
print(line)
