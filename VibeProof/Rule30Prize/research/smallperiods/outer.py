# In the trap regime of driver w, collect the outer-region patterns (columns k+1..k+L) at each phase mod 8
import sys, random
from collections import Counter
w = sys.argv[1]; width = int(sys.argv[2]); steps = int(sys.argv[3]); k = int(sys.argv[4]); L = int(sys.argv[5]); trials = int(sys.argv[6]); tstart = int(sys.argv[7])
P = 8
cnt = [Counter() for _ in range(P)]
for seed in range(trials):
    random.seed(seed)
    init = random.getrandbits(width) | (1 << (width-1))
    row = init; W = width
    for t in range(steps):
        if t >= tstart:
            pat = ''.join(str((row >> (k + i)) & 1) for i in range(L))  # columns k+1 .. k+L (bit i <-> p=i+1)
            colk = (row >> (k-1)) & 1
            cnt[t % P][(colk, pat)] += 1
        W += 1; mask = (1 << W) - 1
        leftn = ((row << 1) | int(w[t % len(w)])) & mask
        row = (leftn ^ (row | (row >> 1))) & mask
for ph in range(P):
    pats = sorted(cnt[ph].items())
    ks = sorted(set(x[0][0] for x in pats))
    print('phase', ph, 'colk values', ks, 'num distinct outer patterns', len(pats))
    allp = set(x[0][1] for x in pats)
    for m in range(1, L+1):
        pre = set(p[:m] for p in allp)
        print('   prefix len', m, 'count', len(pre), 'missing', sorted(set(format(i,'0%db'%m) for i in range(2**m)) - pre)[:12] if len(pre) < 2**m else '')
