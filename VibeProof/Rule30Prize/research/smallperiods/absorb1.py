# Exhaustive check: right half with c(t)=1 for t=0..n-1, from all configurations on cells 1..n+2: is (b,e)=(cell(n,1),cell(n,2))=(0,1)?
import itertools
def run(cfg, n):
    row = list(cfg)  # row[i] = cell at position i+1
    for t in range(n):
        L = len(row)
        new = []
        for i in range(L):
            left = 1 if i == 0 else row[i-1]
            right = row[i+1] if i + 1 < L else 0
            new.append(left ^ (row[i] | right))
        row = new
    return row[0], row[1]
for n in range(1, 12):
    width = n + 2
    bad = 0
    for bits in range(1 << width):
        cfg = [(bits >> i) & 1 for i in range(width)]
        if run(cfg, n) != (0, 1): bad += 1
    print('steps', n, 'configs not absorbed', bad, 'of', 1 << width)
