# Independent brute-force check of Lemma A for rule 30: new = left xor (center or right).
# Boundary column m is black at times s..s+K-1. Columns m+1..m+W at time s arbitrary.
# Report which of (cell(s+K, m+1), cell(s+K, m+2)) are forced.
import itertools
def rule(a, b, c): return a ^ (b | c)
def run(row, K):
    # row[i] = column m+1+i ; boundary (column m) = 1 during these K steps
    for _ in range(K):
        new = []
        for i in range(len(row) - 1):
            left = 1 if i == 0 else row[i - 1]
            new.append(rule(left, row[i], row[i + 1]))
        row = new
    return row
for K in range(1, 12):
    W = K + 2
    seen = set()
    seen01 = set()
    for bits in itertools.product((0, 1), repeat=W):
        out = run(list(bits), K)
        seen.add((out[0], out[1]))
    print(f"K={K} black steps: possible (col m+1, col m+2) at time s+K: {sorted(seen)}")
