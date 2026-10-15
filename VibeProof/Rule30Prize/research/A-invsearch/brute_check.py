import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import death
best = {}
for W in range(1, 17):
    m = -1
    for x in range(1 << (W - 1), 1 << W):   # width exactly W
        d = death(x, 1000)
        if d > m: m = d
    best[W] = max(m, best.get(W - 1, -1))
print('brute-force M(W) (width<=W), W=1..16:', [best[W] for W in range(1, 17)])
