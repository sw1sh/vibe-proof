# Sanity check of the realization lemma: given ANY right half R (p>=1) and ANY periodic driver word w,
# build the left half L by left-permutive reconstruction from y (col_{-1}) so that column 0 = w^inf,
# then run plain rule 30 on the full row and confirm column 0 really is w^inf.
import random, sys
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
w = sys.argv[1]; P = len(w); S = 300           # steps to check
c = [int(w[t % P]) for t in range(3*S + 5)]
# right half: random finite state, evolve driven by c
R = [random.getrandbits(1) for _ in range(150)] + [0]*(3*S)
cols_R = []
row = R[:]
for t in range(2*S + 2):
    cols_R.append(row[0])                      # column 1 at time t
    new = [0]*len(row)
    for i in range(len(row)):
        l = c[t] if i == 0 else row[i-1]; m = row[i]; r = row[i+1] if i+1 < len(row) else 0
        new[i] = l ^ (m | r)
    row = new
# y = column -1: forced by consistency at column 0
y = [(1 - c[t+1]) if c[t] == 1 else (c[t+1] ^ cols_R[t]) for t in range(2*S + 1)]
# reconstruct columns -m at time 0 (left half state) via col_{-m-1}(t) = col_{-m}(t+1) ^ (col_{-m}(t) | col_{-m+1}(t))
colsL = {0: c[:2*S+1], 1: y[:]}
for m in range(1, S + 1):
    a, b = colsL[m], colsL[m-1]
    colsL[m+1] = [a[t+1] ^ (a[t] | b[t]) for t in range(len(a)-1)]
L = [colsL[m][0] for m in range(1, S + 1)]     # positions -1..-S at time 0
# full row: positions -S..-1, 0, 1..len(R)
full = L[::-1] + [c[0]] + R
off = S
ok = True
for t in range(S - 2):
    if full[off] != c[t]: ok = False; print("mismatch at", t); break
    new = [0]*len(full)
    for i in range(len(full)):
        l = full[i-1] if i > 0 else 0; m = full[i]; r = full[i+1] if i+1 < len(full) else 0
        new[i] = l ^ (m | r)
    full = new
print(f"w={w}: column 0 equals w^inf for {S-2} steps: {ok}; left half density {sum(L)/len(L):.2f}, last 20 of L: {L[-20:]}")
