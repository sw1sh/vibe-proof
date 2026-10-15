import sys, itertools
K = int(sys.argv[1]); ph = int(sys.argv[2])
def row_for(alpha):
    n = 2 * K + 2
    c = [(t + ph) % 2 for t in range(n + 2)]
    a = []; it = iter(alpha)
    for t in range(n + 1):
        if c[t] == 1: a.append(1 - c[t + 1])
        else:
            try: a.append(next(it))
            except StopIteration: a.append(None)
    cols = [c[:n+1], a]
    while len(cols[-1]) > 1:
        xp, xq = cols[-1], cols[-2]
        cols.append([None if (xp[t] is None or xp[t+1] is None or xq[t] is None) else xp[t+1] ^ (xp[t] | xq[t]) for t in range(len(xp)-1)])
    return [cols[k][0] for k in range(1, len(cols))]
rows = [row_for(al) for al in itertools.product([0,1], repeat=K)]
L = min(len([v for v in r if v is not None]) for r in rows)
# odd positions (1-based n odd) are 'free' coordinates (check bijection)
oddpos = [n for n in range(1, L+1) if n % 2 == (1 if ph == 0 else 0)]
print('row length', L, 'free positions', oddpos[:12])
for n in range(1, L + 1):
    if n in oddpos: continue
    prev_odd = [j for j in oddpos if j < n]
    table = {}
    for r in rows:
        key = tuple(r[j-1] for j in prev_odd)
        table.setdefault(key, set()).add(r[n-1])
    if any(len(v) > 1 for v in table.values()):
        print('pos -%d: NOT a function of earlier free cells' % n); continue
    tab = {k: next(iter(v)) for k, v in table.items()}
    keys = list(tab)
    support = []
    for idx, j in enumerate(prev_odd):
        for k in keys:
            k2 = list(k); k2[idx] ^= 1; k2 = tuple(k2)
            if k2 in tab and tab[k2] != tab[k]: support.append(j); break
    proj = {}
    for k, v in tab.items():
        proj[tuple(k[prev_odd.index(j)] for j in support)] = v
    s = ''
    if len(support) <= 3: s = str(sorted(proj.items()))
    print('pos -%d = f(-%s) %s' % (n, support, s))
