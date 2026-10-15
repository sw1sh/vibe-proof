# For driver w^inf on the right half (random initial state), find how many columns near the boundary are
# eventually periodic, and print the boundary layer pattern over one period.
import sys, random
def rows_right(cvals, init):
    row = init; rows = []
    W = max(init.bit_length(), 1) + len(cvals) + 2
    mask = (1 << W) - 1
    for t, ct in enumerate(cvals):
        rows.append(row)
        row = ((((row << 1) | ct) & mask) ^ (row | (row >> 1))) & mask
    return rows
w = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3])
random.seed(seed)
init = random.getrandbits(400) if seed else 0
P = len(w)
c = [int(w[t % P]) for t in range(steps)]
rows = rows_right(c, init)
def colseq(p, a, b): return [(rows[t] >> (p - 1)) & 1 for t in range(a, b)]
a = steps // 2
for p in range(1, 40):
    s = colseq(p, a, steps)
    per = None
    for Q in range(P, 40 * P + 1, P):
        if all(s[i] == s[i + Q] for i in range(len(s) - Q)): per = Q; break
    print(p, per, end='; ')
print()
# show the layer: last few periods for columns 1..20
for t in range(steps - 3 * 4 * P, steps):
    print(t % P, c[t], ''.join('#' if (rows[t] >> i) & 1 else '.' for i in range(24)))
