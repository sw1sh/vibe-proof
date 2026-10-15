# Starting right after a black run of length >= 9 (strip in the black-run attractor), feed a pattern and
# report whether col_1 is forced (single possible value) at every white time of the pattern.
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
b = int(sys.argv[1])
A = set(range(1 << b))
for _ in range(40): A = step_set(A, 1, b)
print("black attractor size", len(A))
def forced(pattern):
    S = set(A); res = []
    for ch in pattern:
        if ch == '0':
            vals = set(s & 1 for s in S)
            res.append(len(vals) == 1)
        S = step_set(S, int(ch), b)
    return all(res), S
print("rows: white run a (after long black run); cols: next black run L; entry: forced at all whites of 0^a 1^L 0^6 ?")
for a in range(1, 9):
    row = ''
    for L in range(1, 9):
        ok, _ = forced('0' * a + '1' * L + '0' * 6)
        row += ' Y' if ok else ' .'
    print(f"a={a}:{row}")
