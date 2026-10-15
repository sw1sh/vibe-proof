# Independent brute-force re-implementation of AbsorbRight.Determined (Lean def), no SAT.
import sys, itertools

def rule(a, b, c):
    return a ^ (b | c)

def step_row(l, row):
    # stepRow l (a :: b :: rest) = rule l a b :: stepRow a (b :: rest); shorter by one
    out = []
    left = l
    for i in range(len(row) - 1):
        out.append(rule(left, row[i], row[i + 1]))
        left = row[i]
    return out

def trace_col1(ds, row):
    tr = []
    for c in ds:
        tr.append(row[0] if row else 0)
        row = step_row(c, row)
    tr.append(row[0] if row else 0)
    return tr

def drv(u):
    return list(u) + [1] * 9

def wb(j):
    return [0, 1] * j

def determined(u, j0):
    n = len(u) + 10 - 2 * j0
    if n < 0:
        return None
    d = drv(u)
    ref = trace_col1(d, wb(j0) + [0] * n)
    for tail in itertools.product((0, 1), repeat=n):
        if trace_col1(d, wb(j0) + list(tail)) != ref:
            return False
    return True

def min_j0(u):
    for j0 in range(0, (len(u) + 10) // 2 + 1):
        if determined(u, j0):
            return j0
    return None

if __name__ == '__main__':
    blocks = []
    for L in range(1, 8):
        for mid in itertools.product((0, 1), repeat=max(L - 2, 0)):
            if L == 1:
                u = (0,)
            else:
                u = (0,) + mid + (0,)
            if u not in blocks:
                blocks.append(u)
    print("number of blocks:", len(blocks))
    table = {}
    for line in open(sys.argv[1]):
        k, v = line.strip().split(':')
        table[k.strip()] = int(v)
    from collections import Counter
    cnt = Counter()
    bad = []
    for u in blocks:
        s = ''.join(map(str, u))
        m = min_j0(u)
        cnt[m] += 1
        claimed = table.get(s)
        ok_claimed = determined(u, claimed) if claimed is not None else None
        if claimed != m or not ok_claimed:
            bad.append((s, m, claimed, ok_claimed))
    print("min j0 counts:", dict(cnt))
    print("table entries:", len(table), "blocks missing from table:", [''.join(map(str,u)) for u in blocks if ''.join(map(str,u)) not in table])
    print("mismatches (block, brute min j0, table j0, Determined(table j0)):", bad)
    # empty block
    print("empty block u=[] min j0:", min_j0(()))
