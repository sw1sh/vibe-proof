# Verifier: decode t001 from the Lean source (own parser), re-check closure as a set property with an
# independent strip step, the U-property, and the described core structure. Writes trap states for C.
import re, sys
sys.set_int_max_str_digits(0)
src = open(sys.argv[1]).read()
val = lambda nm: int(re.search(r"^def %s : Nat := (\d+)\s*$" % nm, src, re.M).group(1))
n, lb, ib, u, R, L = val("t001_n"), val("t001_lb"), val("t001_ib"), val("t001_u"), val("t001_R"), val("t001_L")
b, m, w = 47, 21, [0, 0, 1]
st = [(R >> (b * i)) & ((1 << b) - 1) for i in range(n)]
lab = [(L >> (lb * i)) & ((1 << lb) - 1) for i in range(n)]
assert R >> (b * n) == 0 and L >> (lb * n) == 0, "extra data beyond n states"
pairs = set(zip(st, lab))
print("states", n, "distinct (strip,label) pairs", len(pairs), "labels <21:", all(l < m for l in lab))
print("distinct strips", len(set(st)), "; strips occurring with >1 label:", sum(1 for s in set(st) if len({l for (x, l) in pairs if x == s}) > 1))
def step(r, left, z):   # bit k = column k+1; new col = left xor (center or right)
    out = 0
    for k in range(b):
        l = left if k == 0 else (r >> (k - 1)) & 1
        c = (r >> k) & 1
        rr = z if k == b - 1 else (r >> (k + 1)) & 1
        out |= (l ^ (c | rr)) << k
    return out
closed = all((step(s, w[l % 3], z), (l + 1) % m) in pairs for (s, l) in pairs for z in (0, 1))
print("closed under both inputs (set property, own step):", closed)
uok = all(w[l % 3] == 1 or (s & 1) == (u >> l) & 1 for (s, l) in pairs)
print("U: column 1 at white phases equals u(label):", uok, " u bits set:", [i for i in range(m) if (u >> i) & 1])
# core: columns 1..k equal across all states with the same label
def maxcore():
    for k in range(b, 0, -1):
        mk = (1 << k) - 1
        if all(len({s & mk for (s, l) in pairs if l == L0}) == 1 for L0 in range(m)): return k
    return 0
k = maxcore(); print("largest k such that columns 1..k are a function of the label:", k)
print("states per label:", [sum(1 for (s, l) in pairs if l == L0) for L0 in range(m)])
# core columns as label-series, compared with the 12x3 ether (any column, any phase shift)
cols = "001 001 011 110 010 010 110 101 100 100 101 011".split()
core = {L0: next(s for (s, l) in pairs if l == L0) for L0 in range(m)}
match = 0
for c in range(k):
    ser = [(core[L0] >> c) & 1 for L0 in range(m)]
    if any(all(ser[L0] == int(cols[j][(L0 + sh) % 3]) for L0 in range(m)) for j in range(12) for sh in range(3)): match += 1
print("core columns equal to some ether column (any shift):", match, "of", k)
per = [min(p for p in range(1, m + 1) if all(((core[L0] >> c) & 1) == ((core[(L0 + p) % m] >> c) & 1) for L0 in range(m))) for c in range(k)]
print("least period (in labels) of each core column:", per)
with open(sys.argv[2], "w") as f:
    f.write("%d %d\n" % (len(pairs), b))
    for (s, l) in sorted(pairs): f.write("%d %d\n" % (s, l))
