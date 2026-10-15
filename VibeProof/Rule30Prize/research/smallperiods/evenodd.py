# Period-2 left-half constraint (*): at time 0 (phase ph: c(t) = (t+ph)%2), express even-position cells of the
# time-0 row as Boolean functions of the odd-position cells (which are in bijection with alpha).
# Enumerate all alpha in {0,1}^K, compute the row, then for each even position check which odd positions it depends on.
import sys, itertools
K = int(sys.argv[1]); ph = int(sys.argv[2])
def row_for(alpha):
    n = 2 * K + 2
    c = [(t + ph) % 2 for t in range(n + 2)]
    a = []
    it = iter(alpha)
    for t in range(n + 1):
        if c[t] == 1: a.append(1 - c[t + 1])
        else:
            try: a.append(next(it))
            except StopIteration: a.append(None)
    cols = [c[:n+1], a]
    while len(cols[-1]) > 1:
        xp, xq = cols[-1], cols[-2]
        new = []
        for t in range(len(xp) - 1):
            if xp[t] is None or xp[t+1] is None or xq[t] is None: new.append(None)
            else: new.append(xp[t+1] ^ (xp[t] | xq[t]))
        cols.append(new)
    return [cols[k][0] for k in range(1, len(cols))]  # x_{-1}(0), x_{-2}(0), ...
rows = {}
for alpha in itertools.product([0, 1], repeat=K):
    r = row_for(alpha)
    rows[alpha] = r
# determine which positions are fully determined (not None) for all alpha
L = min(len([v for v in r if v is not None]) for r in rows.values())
# keys: tuple of row values at 'free' positions; we want: position n as function of positions < n
print('determined row length', L)
for n in range(1, L + 1):
    # find minimal set S of earlier positions (1..n-1) such that row[n-1] is a function of row[S]
    # check dependence: n-th cell vs all earlier cells: is it a function of earlier cells?
    table = {}
    func = True
    for r in rows.values():
        key = tuple(r[:n-1]); v = r[n-1]
        if key in table and table[key] != v: func = False; break
        table[key] = v
    if not func:
        print('pos -%d: free (not a function of earlier cells)' % n); continue
    # find which earlier positions matter: a position j matters if flipping it changes the function on some pair present
    keys = list(table.keys())
    kset = set(keys)
    support = []
    for j in range(n - 1):
        dep = False
        for k in keys:
            k2 = list(k); k2[j] ^= 1; k2 = tuple(k2)
            if k2 in kset and table[k2] != table[k]: dep = True; break
        if dep: support.append(j + 1)
    # check if function is determined by support only
    proj = {}
    ok = True
    for k, v in table.items():
        pk = tuple(k[j-1] for j in support)
        if pk in proj and proj[pk] != v: ok = False; break
        proj[pk] = v
    print('pos -%d: function of positions -%s %s; table %s' % (n, support, '' if ok else '(NOT determined by support alone)', sorted(proj.items()) if len(support) <= 4 else ''))
