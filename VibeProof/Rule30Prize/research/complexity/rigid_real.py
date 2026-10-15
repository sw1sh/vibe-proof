# Rigidity of left columns under period 2 when s = col_{-1}(odd) ranges over complements of right-realizable words.
import sys
words = [l.strip() for l in open(sys.argv[1])]
M = int(sys.argv[2])
n = len(words[0])
vals = {}
for zw in words:
    s = [1 - int(ch) for ch in zw]
    J = 2 * n
    c = [1 if j % 2 == 0 else 0 for j in range(J + 1)]
    cols = {0: c[:J], 1: [1 if j % 2 == 0 else s[j // 2] for j in range(J)]}
    for m in range(1, M):
        a, b = cols[m], cols[m - 1]
        cols[m + 1] = [a[j + 1] ^ (a[j] | b[j]) for j in range(len(a) - 1)]
    for m in range(1, M + 1):
        for j in range(len(cols[m])):
            vals.setdefault((m, j), set()).add(cols[m][j])
for m in range(1, M + 1):
    row = []
    for j in range(0, 2 * n - M):
        v = vals.get((m, j))
        row.append('?' if v is None else (str(next(iter(v))) if len(v) == 1 else '*'))
    print(f"col -{m:2d}: " + ''.join(row))
