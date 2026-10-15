# Least periods 2^{e_j} of right diagonals R_j, j <= 47, from rows t < 2^E (decisive when e_j <= E).
import sys
E = int(sys.argv[1]); TM = 1 << E; N = TM + 64; JM = 47
x = 1 << N; cols = [[] for _ in range(JM + 1)]
for t in range(TM):
    y = x >> (N + t - JM)            # bits for positions t-JM .. t (and above, which are 0 beyond t)
    for j in range(JM + 1): cols[j].append((y >> (JM - j)) & 1)
    x = (x << 1) ^ (x | (x >> 1))
ej = []
for j in range(JM + 1):
    f = cols[j]; found = None
    for e in range(E + 1):
        P = 1 << e
        if P > TM: break
        if all(f[t + P] == f[t] for t in range(TM - P)): found = e; break
    ej.append(found)
brief = list(map(int, "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18".split()))
print("computed:", ej)
print("first disagreement with brief:", next((j for j in range(JM + 1) if ej[j] != brief[j]), None))
