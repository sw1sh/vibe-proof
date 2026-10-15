# Independent check: (1) c7 (black at p = 6 mod 7) is the 7x4 ether of B-edge-trap;
# (2) the ether's left half, with column 0 = the alternating B4 column, is a ZBL orbit
#     satisfying the period-2 constraints, with free bits f alternating, and f = not(col 1 at white times).
def rule(l, c, r): return l ^ (c | r)
N = 7
row = [1 if p % 7 == 6 else 0 for p in range(N)]          # one period of c7, cyclic
rows = [row]
for t in range(12):
    r = rows[-1]
    rows.append([rule(r[(p - 1) % N], r[p], r[(p + 1) % N]) for p in range(N)])
print("temporal period 4:", rows[4] == rows[0], " period 2?", rows[2] == rows[0])
cols = [''.join(str(rows[t][p]) for t in range(4)) for p in range(N)]
print("columns of c7 (p=0..6, phases 0..3):", cols)
ether = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']   # B1..B5,c,c from the claim
# find cyclic shift (space) and time shift aligning c7 columns with the ether
found = []
for ds in range(7):
    for dt in range(4):
        ok = all(''.join(cols[(j + ds) % 7][(ph + dt) % 4] for ph in range(4)) == ether[j] for j in range(7))
        if ok: found.append((ds, dt))
print("c7 == ether up to (space shift, time shift):", found)
# center = B4 column (alternating). Left half = columns j < 3 (B3 at -1, B2 at -2, ...).
ds, dt = found[0]
E = lambda j, ph: int(cols[(j + ds) % 7][(ph + dt) % 4])
# alternating center c(ph) = E(3, ph): 0101 ; effective boundary c & c(t+1) = 0 always
c = [E(3, ph) for ph in range(4)]
eff = [c[ph] & c[(ph + 1) % 4] for ph in range(4)]
print("center B4:", c, " effective boundary c'(t)=c(t)&c(t+1):", eff)
# ZBL check on a long window of the left half: x_k(t) = E(3-k, t), wall x_0 = 0
ok = True
for t in range(8):
    for k in range(1, 40):
        lhs = E(3 - k, t + 1)
        rhs = rule(E(3 - k - 1, t), E(3 - k, t), 0 if k == 1 else E(3 - k + 1, t))
        ok &= (lhs == rhs)
print("left half of ether evolves as ZBL with white wall:", ok)
black = [ph for ph in range(4) if c[ph] == 1]; white = [ph for ph in range(4) if c[ph] == 0]
print("col -1 at black-center phases", [E(2, ph) for ph in black], "(must be all 1)")
print("free bits f (col -1 at white-center phases)", [E(2, ph) for ph in white],
      " col +1 at white phases", [E(4, ph) for ph in white],
      " f == not col1:", all(E(2, ph) == 1 - E(4, ph) for ph in white))
