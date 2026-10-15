# (1) Rules 210 and 154 from a single seed reproduce rule 90's pattern exactly (sublattice argument).
# (2) Sanity check of the identity x_{-1}(t) = c(t+1) xor c(t) xor (x_1(t) and not c(t)) for rule 30.
N = 1500
def evolve(rule, N):
    width = 2 * N + 5; off = N + 2
    row = [0] * width; row[off] = 1
    rows = [row]
    for t in range(N):
        new = [0] * width
        for i in range(1, width - 1):
            new[i] = (rule >> (4 * row[i - 1] + 2 * row[i] + row[i + 1])) & 1
        row = new; rows.append(row)
    return rows, off
r90, off = evolve(90, N)
for rule in (210, 154):
    rr, _ = evolve(rule, N)
    print('rule', rule, 'identical to rule 90 pattern for', N, 'steps:', rr == r90)
r30, off = evolve(30, N)
ok = all(r30[t][off - 1] == (r30[t + 1][off] ^ r30[t][off] ^ (r30[t][off + 1] & (1 - r30[t][off]))) for t in range(N))
print('rule 30 identity x_{-1} = c(t+1) xor c(t) xor (x_1 and not c):', ok)
