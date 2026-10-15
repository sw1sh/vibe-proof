import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-theoremB-cx')
import theoremB_driven as M
rng = random.Random(5)
for u in [(0,), (0,1,1,0), tuple([0]*20)]:
    import math
    r = 9*math.ceil((len(u)+9)/2)
    fails, traces, P, j = M.run_case(u, r, rng, 'random', pre_mode='real')
    print(u, 'r', r, 'P', P, 'j', j, 'fails', len(fails), 'ntraces', len(traces), 'trace', ''.join(map(str, traces[0][1])))
