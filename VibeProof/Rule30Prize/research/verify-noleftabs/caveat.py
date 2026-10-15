# Caveat check: outside the claim's hypotheses (finite support, leftmost black cell), column -1 CAN be periodic.
def run(s, c, T, W):
    # s: dict p->bit for p in [-W,-1]; positions < -W treated via padding function pad(p)
    row = {p: s(p) for p in range(-W-T-2, 0)}
    col = []
    for t in range(T):
        col.append(row[-1])
        new = {}
        for p in range(-W-T-1+t, 0):
            l = row.get(p-1, s(p-1) if t == 0 else None)
            if l is None: continue
            r = c(t) if p+1 == 0 else row[p+1]
            new[p] = row[p-1] ^ (row[p] | r)
        row = new
    return col
alt = lambda p: 1 if p % 2 == 0 else 0
print("alt start, c=1:", run(alt, lambda t: 1, 40, 10)[:40])
print("zero start, c=0:", run(lambda p: 0, lambda t: 0, 20, 10))
