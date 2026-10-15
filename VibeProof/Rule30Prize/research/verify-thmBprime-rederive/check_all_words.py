import itertools, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-thmBprime-rederive')
from check_det_lib import determined
fails = []
tot = 0
for n in range(0, 8):
    for v in itertools.product([0, 1], repeat=n):
        tot += 1
        if not determined(v, 4):
            fails.append(''.join(map(str, v)))
print("words of length 0..7:", tot, "failing Determined(v,4):", len(fails))
print(fails[:60])
