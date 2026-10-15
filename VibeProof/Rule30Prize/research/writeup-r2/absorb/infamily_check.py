#!/usr/bin/env python3
"""Independent check of ether+wall family entry (Lean R30EtherWall.InFamily, 109 Lean wall states) for the
true rule-30 right half at time T, driven by w^inf in each of the 4 phases. Prints the first entry time per phase."""
import re, sys
src = open(sys.argv[1]).read()
blk = src[src.index('def wallStates'):]; blk = blk[:blk.index(']\n\n') + 1]
walls = set()
for ph, lst in re.findall(r'\((\d+),\s*\[([^\]]*)\]\)', blk):
    bits = tuple(1 if b.strip() == 'true' else 0 for b in lst.split(','))
    walls.add((int(ph), bits))
assert len(walls) == 109
table = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
ether = lambda j, ph: int(table[j % 7][ph % 4])
rule = lambda l, c, r: l ^ (c | r)
w = sys.argv[2]; Ts = [int(x) for x in sys.argv[3].split(',')]; S = int(sys.argv[4])
al = [(j0, s) for j0 in range(7) for s in range(4) if all(ether(j0, ps + s) == int(w[ps]) for ps in range(4))]
def true_row(T):
    W = 2 * T + 5; off = T + 2
    r = [0] * W; r[off] = 1
    for t in range(T):
        r = [0] + [rule(r[p - 1], r[p], r[p + 1]) for p in range(1, W - 1)] + [0]
    return [r[off + p] for p in range(0, T + 2)]   # columns 0..T+1
for T in Ts:
    res = []
    for phi in range(4):
        base = true_row(T)
        Wd = T + S + 40
        row = [int(w[phi % 4])] + base[1:] + [0] * (Wd - len(base))
        first = None
        for t1 in range(S + 1):
            psi = (t1 + phi)
            for (j0, s) in al:
                for k in range(0, 60):
                    if (j0 + k) % 7 != 2: continue
                    if all(row[p] == ether(j0 + p, psi + s) for p in range(1, k + 1)) and \
                       (((psi + s) % 4), tuple(row[k + 1:k + 14])) in walls:
                        first = t1; break
                if first is not None: break
            if first is not None: break
            nxt = [int(w[(t1 + 1 + phi) % 4])] + [rule(row[p - 1], row[p], row[p + 1] if p + 1 < len(row) else 0) for p in range(1, len(row))]
            row = nxt
        res.append(first)
    print(f"w={w} T={T}: first entry per phase {res}, max {max(x for x in res if x is not None) if all(x is not None for x in res) else 'NONE'}")
