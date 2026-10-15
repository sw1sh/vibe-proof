# Independent dict-based simulation of the driven left half; compare to Lean D and to left_driven.run_left
import sys
def sim(x, c, steps, W):
    # x: dict p->bit for p<=-1 (finite support), c: function; returns rows[t] as dict p->bit for p in [-W,-1]
    rows = []
    row = {p: x.get(p, 0) for p in range(-W - steps - 2, 0)}
    for t in range(steps):
        rows.append(dict(row))
        new = {}
        lo = min(row)
        for p in range(lo + 1, 0):
            r = c(t) if p + 1 == 0 else row[p + 1]
            new[p] = row[p - 1] ^ (row[p] | r)
        row = new
    return rows
def drv(w):
    return lambda t: 1 if t == 0 else int(w[(t - 1) % len(w)])
for w, m in [("01", 1), ("001", 1), ("0111", 2), ("1101000", 3)]:
    rows = sim({}, drv(w), 12, 5)
    print(w, -m, "".join(str(rows[t][-m]) for t in range(12)))
