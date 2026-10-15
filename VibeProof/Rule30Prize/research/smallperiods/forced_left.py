# Over all valid column-1 words (right half driven by alternating c, c(0)=0), compute the left-permutive
# extension (with a = c(t+1) xor (c(t) or b(t))) and report cells x_{-n}(t) that are constant over all words.
import sys
fn = sys.argv[1]; L = int(sys.argv[2])
words = [l.strip() for l in open(fn)]
c = [t % 2 for t in range(L + 2)]
tables = []
for w in words:
    b = [int(ch) for ch in w[:L]]
    a = [c[t+1] ^ (c[t] | b[t]) for t in range(L)]
    cols = {0: c[:L], -1: a}
    n = -1
    while len(cols[n]) > 1:
        xp, xq = cols[n], cols[n+1]
        cols[n-1] = [xp[t+1] ^ (xp[t] | xq[t]) for t in range(len(xp) - 1)]
        n -= 1
    tables.append(cols)
maxn = min(len(T) for T in tables) - 1
for n in range(1, maxn):
    L_n = len(tables[0][-n])
    line = ''
    for t in range(L_n):
        vals = set(T[-n][t] for T in tables)
        line += str(next(iter(vals))) if len(vals) == 1 else '*'
    print('col -%2d: %s' % (n, line))
