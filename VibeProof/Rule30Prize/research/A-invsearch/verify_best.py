import re, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import death
ok = True
for line in open(sys.argv[1]):
    m = re.search(r'W=(\d+) maxdeath=(\d+).*cfg\(depth1..W\)=([01]+)', line)
    if not m: continue
    W, md, cfg = int(m.group(1)), int(m.group(2)), m.group(3)
    x = sum(1 << i for i, b in enumerate(cfg) if b == '1')
    d = death(x, 10000)
    if d != md: ok = False; print('MISMATCH', W, md, d, cfg)
print('all best configurations re-simulated; consistent =', ok)
