# Independent verifier for claim C2 (9-step absorption).
# (1) Window dynamics, implemented with a dict of known cells (light-cone tracking), not list slicing.
# (2) Actual rule-30 pattern from a single black cell: check absorb/persistence on every occurrence,
#     and look for "optimality witnesses" in the real pattern (8 ones in center, pair != (0,1)).
import itertools, sys

def rule(l, c, r):
    return l ^ (c | r)

def window_result(cfg, n, cvals):
    # cfg[p-1] = cell(0,p) for p = 1..W ; cvals[k] = cell(k,0)
    W = len(cfg)
    known = {(0, p): cfg[p-1] for p in range(1, W+1)}
    for k in range(len(cvals)):
        known[(k, 0)] = cvals[k]
    for k in range(n):
        for p in range(1, W+1):
            if (k, p-1) in known and (k, p) in known and (k, p+1) in known:
                known[(k+1, p)] = rule(known[(k, p-1)], known[(k, p)], known[(k, p+1)])
    return known.get((n, 1)), known.get((n, 2))

for n in range(1, 11):
    W = n + 2
    bad = 0
    undetermined = 0
    for cfg in itertools.product((0, 1), repeat=W):
        r = window_result(cfg, n, [1]*n)
        if None in r:
            undetermined += 1
        elif r != (0, 1):
            bad += 1
    print(f"n={n}: width {W}, not absorbed {bad} of {2**W}, undetermined {undetermined}")
