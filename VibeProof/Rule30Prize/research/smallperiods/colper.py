import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/smallperiods')
from rdriven import run_right, eventual_period
w = sys.argv[1]; width = int(sys.argv[2]); steps = int(sys.argv[3]); ncols = int(sys.argv[4]); seed = int(sys.argv[5])
random.seed(seed)
init = random.getrandbits(width) | (1 << (width-1))
out, _ = run_right(init, width, lambda t: int(w[t % len(w)]), steps, cols=tuple(range(1, ncols+1)))
for k in range(1, ncols+1):
    print(k, eventual_period(out[k], maxP=steps//3))
