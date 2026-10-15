# Sanity check of Lemma A inside the actual rule-30 pattern (single black cell), all columns.
N = 6000
off = N + 4
row = 1 << off                      # bit off <-> column 0
rows = [row]
for t in range(N):
    x = rows[-1]
    rows.append((x << 1) ^ (x | (x >> 1)))   # new_p = old_{p-1} xor (old_p or old_{p+1})
# check center column prefix against A051023
c = [(rows[t] >> off) & 1 for t in range(20)]
assert c == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], c
viol = 0; hits = 0
for t in range(9, N + 1):
    A = rows[t-9]
    for d in range(1, 9):
        A &= rows[t-9+d]
    # column p black at t-9..t-1  =>  cell(t, p+1) = 0 and cell(t, p+2) = 1
    # column p+1 is bit b+1, i.e. (A << 1)
    if (A << 1) & rows[t]: viol += 1
    if (A << 2) & ~rows[t]: viol += 1
    hits += bin(A).count("1")
print("instances of 9-black column segments:", hits, "violations:", viol)
