# Independent brute-force re-derivation of the finite facts used by Theorem B'.
# Rule 30: new = left XOR (center OR right).
import itertools, sys

def rule(l, c, r):
    return l ^ (c | r)

def evolve_right(row, drivers):
    """row: values at columns 1..L at time e (list of 0/1).
    drivers: values of column 0 at times e, e+1, ..., e+n-1.
    Returns column-1 values at times e .. e+n (n+1 values), computed on the
    shrinking light cone (requires L >= n+1)."""
    assert len(row) >= len(drivers) + 1
    cur = list(row)
    out = [cur[0]]
    for d in drivers:
        nxt = []
        for i in range(len(cur) - 1):
            left = d if i == 0 else cur[i - 1]
            nxt.append(rule(left, cur[i], cur[i + 1]))
        cur = nxt
        out.append(cur[0])
    return out


def determined(u, j0):
    """u: tuple of 0/1. Every row of length |u|+10 whose first 2*j0 cells read (0 1)^j0
    gives the same column-1 trace under driver u ++ 1^9."""
    L = len(u) + 10
    if 2 * j0 > L:
        return None
    drv = list(u) + [1] * 9
    pref = [0, 1] * j0
    traces = set()
    for tail in itertools.product([0, 1], repeat=L - 2 * j0):
        traces.add(tuple(evolve_right(pref + list(tail), drv)))
        if len(traces) > 1:
            return False
    return True

