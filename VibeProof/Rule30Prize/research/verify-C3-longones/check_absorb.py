# Independent brute-force checks for C3 (verifier, rigor lens).
import itertools, random

def rule(l, c, r):
    return l ^ (c | r)

def step_right(c0, cols):
    # cols = values at columns 1..n; c0 = column 0. Returns columns 1..n-1 at next step.
    full = [c0] + cols
    return [rule(full[i - 1], full[i], full[i + 1]) for i in range(1, len(cols))]

# 1. absorption: 9 black center steps send every x1..x11 to (0, 1)
def absorb_result(k, n):
    outs = set()
    for bits in itertools.product([0, 1], repeat=n):
        w = list(bits)
        for _ in range(k):
            w = step_right(1, w)
        outs.add(tuple(w[:2]))
    return outs

print("k=9, n=11 ->", absorb_result(9, 11))
for k in range(1, 12):
    print("k=%d (window n=k+2) -> outcomes of (col1,col2):" % k, sorted(absorb_result(k, k + 2)))

# 2. true rule 30 pattern: whenever c(u..u+8)=1, check (cell(u+9,1), cell(u+9,2)) = (0,1)
N = 6000
W = 2 * N + 3
row = [0] * W
mid = N + 1
row[mid] = 1
rows_c, rows_1, rows_2, rows_m1 = [], [], [], []
for t in range(N):
    rows_c.append(row[mid]); rows_1.append(row[mid + 1]); rows_2.append(row[mid + 2]); rows_m1.append(row[mid - 1])
    row = [0] + [rule(row[i - 1], row[i], row[i + 1]) for i in range(1, W - 1)] + [0]
c = rows_c
print("center prefix:", c[:20])
hits = 0
for u in range(N - 10):
    if all(c[u + i] for i in range(9)):
        hits += 1
        assert (rows_1[u + 9], rows_2[u + 9]) == (0, 1), u
print("true-pattern absorb instances checked:", hits)
# cell_left identity on the true pattern
for t in range(N - 1):
    assert rows_m1[t] == c[t + 1] ^ (c[t] | rows_1[t])
print("cell_left identity at column 0 holds for t <", N - 1)
