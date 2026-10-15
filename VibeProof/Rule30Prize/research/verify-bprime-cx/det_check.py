# Independent re-implementation of the Lean definitions in AbsorbRight.lean (Theorem B').
# rule l a b = l xor (a or b); stepRow; traceCol1; drv; wbPattern; Determined.
import itertools, sys, time

def rule(l, a, b):
    return l ^ (a | b)

def stepRow(l, row):
    # stepRow l (a :: b :: rest) = rule l a b :: stepRow a (b :: rest); else []
    out = []
    for i in range(len(row) - 1):
        left = l if i == 0 else row[i - 1]
        out.append(rule(left, row[i], row[i + 1]))
    return out

def traceCol1(ds, row):
    tr = []
    for c in ds:
        tr.append(row[0] if row else 0)
        row = stepRow(c, row)
    tr.append(row[0] if row else 0)
    return tuple(tr)

def drv(u):
    return list(u) + [1] * 9

def wb(j):
    return [0, 1] * j

def determined(u, j0):
    L = len(u) + 10 - 2 * j0
    assert L >= 0
    d = drv(u)
    ref = traceCol1(d, wb(j0) + [0] * L)
    for tail in itertools.product((0, 1), repeat=L):
        if traceCol1(d, wb(j0) + list(tail)) != ref:
            return False
    return True

def min_j0(u):
    for j in range(0, (len(u) + 10) // 2 + 1):
        if determined(u, j):
            return j
    return None

if __name__ == '__main__':
    t0 = time.time()
    table = {}
    with open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/absorb-right/j0_table.txt') as f:
        for line in f:
            if ':' in line:
                k, v = line.split(':')
                table[k.strip()] = int(v)
    blocks = []
    for n in range(1, 8):
        for bits in itertools.product((0, 1), repeat=n):
            if bits[0] == 0 and bits[-1] == 0:
                blocks.append(bits)
    print('number of blocks', len(blocks))
    counts = {}
    mism = 0
    for u in blocks:
        s = ''.join(map(str, u))
        j = min_j0(u)
        counts[j] = counts.get(j, 0) + 1
        tj = table.get(s)
        # check claimed table value is valid (Determined true) and minimal
        ok_claim = tj is not None and determined(u, tj)
        if tj != j or not ok_claim:
            mism += 1
            print('MISMATCH', s, 'min_j0=', j, 'table=', tj, 'Determined(table)=', ok_claim)
    print('counts of minimal j0:', dict(sorted(counts.items())))
    print('table entries:', len(table), 'mismatches:', mism)
    # also: u = [] (pure black) for interest
    print('u=[] min j0:', min_j0(()))
    print('time %.1fs' % (time.time() - t0))
