import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from rsim import true_rows, run, eventual_period
import random

def lyndon(n):
    res = []
    for x in range(2**n):
        s = format(x, '0%db' % n)
        if all(s < s[i:] + s[:i] for i in range(1, n)): res.append(s)
    return res

steps = int(sys.argv[1]); nmin = int(sys.argv[2]); nmax = int(sys.argv[3])
Ts = [int(x) for x in sys.argv[4].split(',')]
rows = {}
for t, rh, c in true_rows(max(Ts)):
    if t in Ts: rows[t] = rh
random.seed(7)
cnt = {'both':0,'e_only':0,'neither':0,'d_only':0, 'mixed':0}
for n in range(nmin, nmax+1):
    for w in lyndon(n):
        res = []
        for T in Ts:
            for ph in range(len(w)):
                ww = w[ph:] + w[:ph]
                cc, d, _ = run(ww, rows[T], steps)
                e = bytes(a | b for a, b in zip(cc, d))
                pd = eventual_period(bytes(d), maxP=256); pe = eventual_period(e, maxP=256)
                res.append((pd is not None, pe is not None))
        dall = all(r[0] for r in res); eall = all(r[1] for r in res)
        dnone = not any(r[0] for r in res); enone = not any(r[1] for r in res)
        tag = ('both' if dall and eall else 'e_only' if eall and not dall else 'neither' if dnone and enone else 'mixed')
        cnt[tag] += 1
        if tag != 'neither':
            print(w, tag, ''.join('11' if a and b else '01' if b else '10' if a else '00' for a, b in res), flush=True)
print(cnt)
