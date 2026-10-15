# Independent brute force of the black-run forcing lemma (driven right half, column 0 held black).
from itertools import product

def rule(a, b, c):
    return a ^ (b | c)

def run_black(row, k):
    # row = values of columns 1..n at time t; column 0 is 1 during k steps
    for _ in range(k):
        ext = [1] + row
        row = [rule(ext[i - 1], ext[i], ext[i + 1]) for i in range(1, len(ext) - 1)]
    return row

for k in range(1, 12):
    n = k + 2
    outs = set()
    for bits in product([0, 1], repeat=n):
        outs.add(tuple(run_black(list(bits), k)))
    print(f"k={k:2d} black steps: possible (col1,col2) after k steps = {sorted(outs)}")
