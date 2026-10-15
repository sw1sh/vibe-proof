# Distribution of the length of the leading pure-ether segment (columns 0..L-1 equal ether columns 6+k mod 7)
# for 0001-driven right halves from random finite prefixes; also the word of the first non-ether column.
import random, sys
from collections import Counter
cols = {0: "0011", 1: "0110", 2: "1101", 3: "0101", 4: "0011", 5: "0001", 6: "0001"}
def run(w, n, dbits, S, K):
    P = len(w)
    drv = lambda t: dbits[t] if t < n else int(w[(t - n) % P])
    row = drv(0); vals = {}
    for t in range(n + S):
        if t >= n + S // 2:
            r = (t - n) % 4
            for k in range(K + 1):
                v = (row >> k) & 1
                vals[(k, r)] = v if vals.get((k, r), v) == v else '*'
        Wd = row.bit_length() + 2
        row = ((((row << 1) ^ (row | (row >> 1))) & ((1 << Wd) - 1)) & ~1) | drv(t + 1)
    return [''.join(str(vals[(k, r)]) for r in range(4)) for k in range(K + 1)]
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
lens = Counter(); nxt = Counter()
for trial in range(N):
    n = random.randint(1, 60)
    d = [random.randint(0, 1) for _ in range(n)]
    words = run("0001", n, d, 1200, 40)
    best = (0, None)
    for j0 in (5, 6):
        L = 0
        while L < len(words) and words[L] == cols[(j0 + L) % 7]: L += 1
        best = max(best, (L, j0))
    L, j0 = best
    lastcol = cols[(j0 + L - 1) % 7]
    lens[(L, j0, 'last=' + lastcol)] += 1; nxt[words[L] if L < len(words) else 'END'] += 1
print("leading ether segment length (incl. column 0) -> count:", sorted(lens.items()))
print("first non-ether column word -> count:", nxt.most_common(8))
