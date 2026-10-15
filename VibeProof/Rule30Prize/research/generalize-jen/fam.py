import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from strip_scan import limit
Kmax = int(sys.argv[1])
for w in sys.argv[2].split(','):
    res = None
    for K in range(4, Kmax + 1):
        vals = limit(w, K)
        ef = all(not (h0 and h1) for (h0, h1), ch in zip(vals, w) if ch == '0')
        if ef:
            res = (K, ''.join('-' if (h0 and h1) else ('0' if h0 else '1') for (h0, h1) in vals)); break
    print(w, res, flush=True)
