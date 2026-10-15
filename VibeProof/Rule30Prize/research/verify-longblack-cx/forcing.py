# Brute-force the black-run forcing lemma for the RIGHT half driven by column 0.
# Right half update (p>=1): x'(p) = x(p-1) XOR (x(p) OR x(p+1)), with x(0) = boundary b(t).
import itertools, random

def step_right(b, row):
    # row = [x1..xL] ; returns [x1'..x_{L-1}'] (light cone shrinks by one on the right)
    full = [b] + row
    return [full[i] ^ (full[i+1] | full[i+2]) for i in range(len(full)-2)]

def run(bs, row):
    for b in bs:
        row = step_right(b, row)
    return row

# 1) exact lemma: all 2^11 rows, 9 black steps -> [0,1]
bad = [r for r in itertools.product([0,1], repeat=11) if run([1]*9, list(r)) != [0,1]]
print("9 black steps, all 2^11 rows: failures =", len(bad))

# 2) minimality: for n black steps (n=1..12) and width n+2, how many rows end at [0,1]?
for n in range(1, 13):
    W = n + 2
    cnt = sum(1 for r in itertools.product([0,1], repeat=W) if run([1]*n, list(r)) == [0,1])
    print(f"n={n:2d} black steps: rows forced to (col1,col2)=(0,1): {cnt}/{2**W}")

# 3) wider random rows (cells beyond the light cone must not matter): width 40, 200k rows
random.seed(1)
fails = 0
for _ in range(200000):
    r = [random.getrandbits(1) for _ in range(40)]
    out = run([1]*9, r)
    if out[:2] != [0,1]:
        fails += 1
print("width-40 random rows, 9 black steps: failures =", fails)

# 4) (0,1) is a fixed point of (col1,col2) under black driving, regardless of col3
for x3 in (0,1):
    for rest in itertools.product([0,1], repeat=3):
        out = step_right(1, [0,1,x3] + list(rest))
        assert out[:2] == [0,1], (x3, rest, out)
print("(col1,col2)=(0,1) stays fixed under further black steps: OK")
