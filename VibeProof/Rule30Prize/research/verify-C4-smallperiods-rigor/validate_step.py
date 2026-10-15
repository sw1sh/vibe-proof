# Validate the strip step against the TRUE rule 30 pattern from a single black cell:
# 1) full CA from the definition reproduces A051023's prefix;
# 2) the encoded strip step, fed the true column 0 and true column W+1, reproduces true columns 1..W.
import sys
sys.path.insert(0, sys.argv[1])
from cert_np import successor_tables

T = 400
W = 12
# full CA on positions -T-2..T+2
off = T + 3
width = 2 * T + 7
row = [0] * width
row[off] = 1
rows = [row[:]]
for t in range(T):
    new = [0] * width
    for i in range(1, width - 1):
        new[i] = row[i - 1] ^ (row[i] | row[i + 1])
    row = new
    rows.append(row[:])
cell = lambda t, p: rows[t][p + off]
c = [cell(t, 0) for t in range(T)]
A051023 = []
for b in open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin','rb').read(50):
    A051023 += [(b >> k) & 1 for k in range(7, -1, -1)]
assert c[:len(A051023)] == A051023, c[:50]
print('center column prefix OK vs center-1e7.bin (%d terms)' % len(A051023))
# Jen-style column-0 consistency
for t in range(T - 1):
    assert c[t + 1] == cell(t, -1) ^ (c[t] | cell(t, 1))
print('column-0 consistency identity OK')
tab = successor_tables(W)
enc = lambda t: sum(cell(t, j) << (W - j) for j in range(1, W + 1))
for t in range(T - 1):
    s = enc(t)
    nxt = int(tab[(c[t], cell(t, W + 1))][s])
    assert nxt == enc(t + 1), t
print('strip step reproduces true columns 1..%d for t < %d' % (W, T - 1))
