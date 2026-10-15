# Independent cross-check of the B1 ether using Wolfram rule numbering (bit (4l+2c+r) of 30).
cols = {0: "0011", 1: "0110", 2: "1101", 3: "0101", 4: "0011", 5: "0001", 6: "0001"}
E = lambda j, ph: int(cols[j % 7][ph % 4])
def r30(l, c, r): return (30 >> (4 * l + 2 * c + r)) & 1
# 1) local orbit check over all residues
bad = [(j, ph) for j in range(7) for ph in range(4)
       if E(j, ph + 1) != r30(E(j - 1, ph), E(j, ph), E(j + 1, ph))]
print("local orbit failures:", bad)
# 2) evolve a long cyclic row (length 7*13) for 100 steps and compare with the table, every offset
for d in range(7):
    row = [E(p + d, 0) for p in range(91)]
    ok = True
    for t in range(1, 101):
        row = [r30(row[p - 1], row[p], row[(p + 1) % 91]) for p in range(91)]
        if row != [E(p + d, t) for p in range(91)]:
            ok = False; break
    print("offset", d, "cyclic evolution matches table for 100 steps:", ok)
# 3) mirrored rule (rule 86 = 30 mirrored) should FAIL, confirming orientation matters and is right
bad86 = [(j, ph) for j in range(7) for ph in range(4)
         if E(j, ph + 1) != r30(E(j + 1, ph), E(j, ph), E(j - 1, ph))]
print("mirror-orientation failures (expected nonempty):", len(bad86))
# 4) alignments, exhaustive: w(psi) = E(j, psi + s)
for w in ["0001", "0011", "0111", "0101"]:
    hits = [(j, s) for j in range(7) for s in range(4) if all(E(j, psi + s) == int(w[psi]) for psi in range(4))]
    print(w, "aligned (column, shift):", hits)
