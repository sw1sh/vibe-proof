import sys, re
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import step, death, col_m1
seen = set()
for line in open('best_mode0.txt'):
    m = re.search(r'W=(\d+) maxdeath=(\d+).*cfg\(depth1..W\)=([01]+)', line)
    W, D, cfg = int(m.group(1)), int(m.group(2)), m.group(3).rstrip('0')
    if cfg in seen: continue
    seen.add(cfg)
    x = sum(1 << i for i, b in enumerate(cfg) if b == '1')
    y = col_m1(x, D + 1)
    f = ''.join(str(y[t]) for t in range(1, D, 2))
    print(f'width {len(cfg):2d} death {D:3d}  cfg={cfg:<42s} f={f}')
