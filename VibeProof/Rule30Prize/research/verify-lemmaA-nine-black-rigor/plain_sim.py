# Plain dict-based rule 30 from a single black cell; no bit tricks.
T = 115
cell = {(0, 0): 1}
def c(t, p): return cell.get((t, p), 0)
for t in range(T):
    for p in range(-t - 1, t + 2):
        l, m_, r = c(t, p - 1), c(t, p), c(t, p + 1)
        v = l ^ (m_ | r)
        if v: cell[(t + 1, p)] = 1
t0, m = 100, 91
print("column", m, "at times", t0, "..", t0 + 7, ":", [c(t0 + s, m) for s in range(8)])
print("cell(t0+8, m+1) =", c(t0 + 8, m + 1), " cell(t0+8, m+2) =", c(t0 + 8, m + 2))
print("column", m, "at time", t0 + 8, ":", c(t0 + 8, m), "(so this 8-run is maximal on the right)" if c(t0+8,m)==0 else "")
print("column", m, "at time", t0 - 1, ":", c(t0 - 1, m))
# brute recheck of the 9-black lemma on this small range
viol = 0; n = 0
for t in range(0, T - 9 + 1):
    for p in range(-t - 1, t + 2):
        if all(c(t + s, p) for s in range(9)):
            n += 1
            if not (c(t + 9, p + 1) == 0 and c(t + 9, p + 2) == 1): viol += 1
print("9-black windows up to T:", n, "violations:", viol)
