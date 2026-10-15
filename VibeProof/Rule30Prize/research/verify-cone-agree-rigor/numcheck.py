# Finite-form sanity check of the cone lemma on the actual rule-30 pattern.
# Weak hypothesis: column 0 agrees for s <= n-2 (all the proof uses), rows agree on 1..n.
T = 420
W = T + 2
off = W
rows = []
row = [0]*(2*W+1); row[off] = 1
rows.append(row)
for t in range(T):
    new = [0]*(2*W+1)
    for i in range(1, 2*W):
        a, b, c = row[i-1], row[i], row[i+1]
        new[i] = a ^ (b | c)
    rows.append(new); row = new
cell = lambda t, p: rows[t][off+p]
center = [cell(t,0) for t in range(T+1)]
assert center[:20] == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1]
inst = 0; viol = 0; sharp = 0
for n in range(2, 13):
    for t0 in range(0, T - n):
        for t1 in range(t0+1, T - n):
            if any(cell(t0,p) != cell(t1,p) for p in range(1, n+1)): continue
            if any(center[t0+s] != center[t1+s] for s in range(0, n-1)): continue
            inst += 1
            for s in range(0, n):
                for p in range(1, n - s + 1):
                    if cell(t0+s,p) != cell(t1+s,p): viol += 1
            # sharpness probe: does agreement already fail just outside the cone (p+s = n+1)?
            if any(cell(t0+s,p) != cell(t1+s,p) for s in range(1, n+1) for p in [n+1-s] if p >= 1):
                sharp += 1
print("nontrivial instances:", inst, "violations:", viol, "instances failing just outside cone:", sharp)
