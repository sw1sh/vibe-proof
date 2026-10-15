# Verifier: independent check of the 12x3 ether, glide, alignments, and uniqueness of (12,3) ethers.
cols = "001 001 011 110 010 010 110 101 100 100 101 011".split()
E = [[int(c[f]) for f in range(3)] for c in cols]          # E[j][phase]
rule = lambda l, c, r: l ^ (c | r)
ok = all(E[j][(f + 1) % 3] == rule(E[(j - 1) % 12][f], E[j][f], E[(j + 1) % 12][f]) for j in range(12) for f in range(3))
print("ether is a rule-30 orbit (ring 12, period 3):", ok)
print("glide E[j+4][f] == E[j][f+1]:", all(E[(j + 4) % 12][f] == E[j][(f + 1) % 3] for j in range(12) for f in range(3)))
for w in ("001", "011"):
    al = [(j, s) for j in range(12) for s in range(3) if all(E[j][(p + s) % 3] == int(w[p]) for p in range(3))]
    print(w, "alignments:", al)
# uniqueness: all spatially 12-periodic rows whose rule-30 orbit has temporal period exactly 3 (least), up to rotation
def step(row):
    n = len(row); return tuple(rule(row[(i - 1) % n], row[i], row[(i + 1) % n]) for i in range(n))
found = set()
for x in range(1 << 12):
    r0 = tuple((x >> i) & 1 for i in range(12))
    r1 = step(r0); r2 = step(r1); r3 = step(r2)
    if r3 == r0 and r1 != r0:
        # least spatial period 12?
        if all(r0[i:] + r0[:i] != r0 for i in (1, 2, 3, 4, 6)):
            canon = min(min(r[i:] + r[:i] for i in range(12)) for r in (r0, r1, r2))
            found.add(canon)
print("distinct (12,3) ethers with least spatial period 12, up to rotation and time shift:", len(found))
print("ether rows (phase 0):", "".join(str(E[j][0]) for j in range(12)), " canonical forms found:", ["".join(map(str, c)) for c in found])
