# In the trap regime of driver w, collect outer-region patterns relative to the trap phase phi0 (time when col k = 0)
import sys, random
from collections import Counter
w = sys.argv[1]; width = int(sys.argv[2]); steps = int(sys.argv[3]); k = int(sys.argv[4]); L = int(sys.argv[5]); trials = int(sys.argv[6]); tstart = int(sys.argv[7])
P = 8
cnt = [set() for _ in range(P)]
colpat = [set() for _ in range(P)]
for seed in range(trials):
    random.seed(seed)
    init = random.getrandbits(width) | (1 << (width-1))
    row = init; W = width
    rows = []
    for t in range(steps):
        rows.append(row)
        W += 1; mask = (1 << W) - 1
        leftn = ((row << 1) | int(w[t % len(w)])) & mask
        row = (leftn ^ (row | (row >> 1))) & mask
    # find phi0: a time t >= tstart where col k is 0
    zs = [t for t in range(tstart, tstart + 8) if not (rows[t] >> (k-1)) & 1]
    if len(zs) != 1: print('seed', seed, 'zeros at', zs); continue
    phi0 = zs[0]
    for t in range(tstart, steps):
        ph = (t - phi0) % P
        pat = ''.join(str((rows[t] >> (k + i)) & 1) for i in range(L))
        cnt[ph].add(pat)
        colpat[ph].add(''.join(str((rows[t] >> i) & 1) for i in range(k)))
for ph in range(P):
    allp = cnt[ph]
    print('phase phi0%+d' % ph, 'trap cols 1..k patterns:', colpat[ph])
    for m in range(1, L+1):
        pre = set(p[:m] for p in allp)
        miss = sorted(set(format(i,'0%db'%m) for i in range(2**m)) - pre)
        print('   len', m, 'present', len(pre), 'missing', miss[:20], '...' if len(miss)>20 else '')
