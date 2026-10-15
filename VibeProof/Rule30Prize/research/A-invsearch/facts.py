import sys, itertools
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import step
# (1) any finite x with x_1 x_2 x_3 = 1 0 1 has (F^2 x)_1 = 1
ok = True
for tail in range(1 << 12):
    x = 0b101 | (tail << 3)
    if not (step(step(x)) & 1): ok = False
print('x starts 101 => G(x)_1 = 1 :', ok)
# (2) which 3-prefixes guarantee G(x)_1 = 1 (x_1 = 1 required)
for p in range(8):
    vals = set(step(step(p | (t << 3))) & 1 for t in range(16))
    print('prefix x1x2x3 =', format(p, '03b')[::-1], '-> G(x)_1 values', vals)
