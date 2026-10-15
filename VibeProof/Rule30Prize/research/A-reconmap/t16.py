import sys, itertools
sys.path.insert(0, '.')
from t15 import future
for s in range(1, 8):
    cls = {}
    for p in itertools.product((0, 1), repeat=s):
        cls.setdefault(future(list(p), 5), []).append(''.join(map(str, p)))
    merged = [v for v in cls.values() if len(v) > 1]
    print('s=%d classes=%d merged groups:' % (s, len(cls)), merged)
