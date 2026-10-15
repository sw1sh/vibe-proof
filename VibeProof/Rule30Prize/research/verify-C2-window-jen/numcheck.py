# Sanity checks for claim C2 on the actual rule-30 pattern from a single black cell.
import sys
T = int(sys.argv[1]) if len(sys.argv) > 1 else 160
OFF = T + 2
rows = []
row = [0] * (2 * OFF + 1); row[OFF] = 1
rows.append(row)
for t in range(T):
    new = [0] * (2 * OFF + 1)
    for p in range(1, 2 * OFF):
        l, c, r = row[p - 1], row[p], row[p + 1]
        new[p] = l ^ (c | r)
    rows.append(new); row = new
def cell(t, p): return rows[t][p + OFF]
def orc(i, t): return cell(t, i) | cell(t, i + 1)
# check center column against OEIS A051023 prefix
pref = [cell(t, 0) for t in range(20)]
assert pref == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], pref
# (a) claim as stated: col i on s<=m, orCol i on s<m, i-m=-t2, t1<t2 -> windows differ
viol = 0; checked = 0
for t2 in range(1, T // 2 + 1):
    for t1 in range(t2):
        for i in range(-t2, T // 2 - t2 + 1):
            m = i + t2
            if t2 + m > T: break
            same = all(cell(t1 + s, i) == cell(t2 + s, i) for s in range(m + 1)) and \
                   all(orc(i, t1 + s) == orc(i, t2 + s) for s in range(m))
            checked += 1
            if same: viol += 1
print("(a) stated form: checked", checked, "triples, violations:", viol)
# (b) alternative reading (both windows s<m): counterexamples?
alt = []
for t2 in range(1, T // 2 + 1):
    for t1 in range(t2):
        for i in range(-t2, T // 2 - t2 + 1):
            m = i + t2
            if t2 + m > T: break
            if all(cell(t1 + s, i) == cell(t2 + s, i) for s in range(m)) and \
               all(orc(i, t1 + s) == orc(i, t2 + s) for s in range(m)):
                alt.append((t1, t2, i, m))
print("(b) alt reading (column on s<m): #counterexamples", len(alt), "e.g.", alt[:6])
alt0 = [(a, b, i, m) for (a, b, i, m) in alt if i == 0]
print("    of which column 0:", alt0[:6])
# (c) is the orCol hypothesis ever needed? column-0 window alone (s<=t2) matching:
only = [(t1, t2) for t2 in range(1, T // 2 + 1) for t1 in range(t2)
        if all(cell(t1 + s, 0) == cell(t2 + s, 0) for s in range(t2 + 1))]
print("(c) col-0 window (s<=t2) alone equal for (t1,t2):", only[:10])
# (d) second-from-left cell is always 1 for t>=1 (used in (b) reasoning)
print("(d) cell(t,-t+1)==1 for 1<=t<=T:", all(cell(t, -t + 1) == 1 for t in range(1, T + 1)))
