import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import death, stripe
# family x0 = S[1..m] . 1  (m odd): extra black cell at depth m+1
res = []
for m in range(1, 1200, 2):
    x = stripe(m) | (1 << m)       # bit m <-> depth m+1
    D = death(x, 10 * m + 100)
    res.append((D - m, m))
res.sort(reverse=True)
print('largest post-arrival survival D - m for x0 = S[1..m].1 (m odd, m < 1200):', res[:12])
import collections
print('distribution of D - m:', sorted(collections.Counter(r[0] for r in res).items()))
