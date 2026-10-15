import sys
from collections import Counter, defaultdict
w = sys.argv[1]; bs = list(map(int, sys.argv[2:]))
P = len(w)
def load(b):
    B = set()
    for line in open(f'bad_{w}_{b}.txt'):
        ph, s, c = map(int, line.split()); B.add((ph, s))
    return B
prev = None
for b in bs:
    B = load(b)
    # per-phase forced cells
    sk = []
    for ph in range(P):
        S = [s for (q, s) in B if q == ph]
        row = ''
        for p in range(1, b + 1):
            vals = set((s >> (p - 1)) & 1 for s in S)
            row += str(vals.pop()) if len(vals) == 1 else '*'
        sk.append(f"{ph}:{row}({len(S)})")
    msg = f"b={b} |B|={len(B)} skeleton " + ' '.join(sk)
    if prev is not None:
        pb, PB = prev
        proj = set((ph, s & ((1 << pb) - 1)) for (ph, s) in B)
        msg += f"\n   proj to b={pb}: {len(proj)} of {len(PB)} (subset: {proj <= PB}); ext counts " + str(Counter(Counter((ph, s & ((1 << pb) - 1)) for (ph, s) in B).values()))
    print(msg)
    prev = (b, B)
