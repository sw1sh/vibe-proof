import sys
from collections import defaultdict
w = sys.argv[1]
P = len(w)
for b in map(int, sys.argv[2:]):
    comps = defaultdict(list)
    for line in open(f'bad_{w}_{b}.txt'):
        ph, s, c = map(int, line.split()); comps[c].append((ph, s))
    allB = [v for c in comps for v in comps[c]]
    def skel(S):
        out = []
        for ph in range(P):
            T = [s for (q, s) in S if q == ph]
            row = ''
            for p in range(1, b + 1):
                vals = set((s >> (p - 1)) & 1 for s in T)
                row += (str(vals.pop()) if len(vals) == 1 else '*') if T else '-'
            out.append(f"{ph}:{row}")
        return ' '.join(out)
    print(f"w={w} b={b} #bad={len(comps)} union skeleton {skel(allB)}")
    for c in comps: print(f"    comp size {len(comps[c])}: {skel(comps[c])}")
