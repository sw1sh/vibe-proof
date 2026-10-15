# Check claim C2 against the actual rule-30 pattern from a single black cell.
import sys
T = int(sys.argv[1])
off = T + 2
x = 1 << off
C, B, E = [], [], []
mask = (1 << (2 * off + 3)) - 1
for t in range(T + 1):
    C.append((x >> off) & 1)
    B.append((x >> (off + 1)) & 1)
    E.append((x >> (off + 2)) & 1)
    x = ((x << 1) ^ (x | (x >> 1))) & mask
# sanity: center prefix A051023
print("prefix", ''.join(map(str, C[:20])))
assert ''.join(map(str, C[:20])) == "11011100110001011001"
# (a) absorption
occ9 = 0
viol9 = 0
for t0 in range(0, T - 9 + 1):
    if all(C[t0 + i] for i in range(9)):
        occ9 += 1
        if (B[t0 + 9], E[t0 + 9]) != (0, 1):
            viol9 += 1
print("runs>=9 windows:", occ9, "violations:", viol9)
# (b) persistence
occp = 0; violp = 0
for t in range(T):
    if C[t] == 1 and B[t] == 0 and E[t] == 1:
        occp += 1
        if (B[t + 1], E[t + 1]) != (0, 1):
            violp += 1
print("persistence occurrences:", occp, "violations:", violp)
# (c) optimality witnesses in the actual pattern, for k = 1..8 consecutive ones
for k in range(1, 9):
    occ = 0; wit = 0; first = None
    for t0 in range(0, T - k + 1):
        if all(C[t0 + i] for i in range(k)):
            occ += 1
            if (B[t0 + k], E[t0 + k]) != (0, 1):
                wit += 1
                if first is None: first = t0
    print(f"k={k}: windows with {k} ones: {occ}, not absorbed: {wit}, first t0: {first}")
