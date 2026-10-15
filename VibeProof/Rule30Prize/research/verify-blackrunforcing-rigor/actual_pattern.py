# Simulate rule 30 from a single black cell with Python big ints; check the black-run lemma on the
# actual pattern and cross-check the center column against the read-only data file.
# Bit (p + T) of R is cell(t, p).  new(p) = old(p-1) ^ (old(p) | old(p+1)).
import sys
T = int(sys.argv[1])
R = 1 << T
cols = []          # (c(t), cell(t,1), cell(t,2)) for t = 0..T
for t in range(T + 1):
    w = (R >> T) & 7
    cols.append((w & 1, (w >> 1) & 1, (w >> 2) & 1))
    R = (R << 1) ^ (R | (R >> 1))
c = [x[0] for x in cols]
# compare with data file (first value in high bit)
with open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb') as f:
    data = f.read((T + 1 + 7) // 8)
filebits = [(data[i // 8] >> (7 - i % 8)) & 1 for i in range(T + 1)]
print("center column matches center-1e7.bin on t=0..%d:" % T, filebits == c)
print("first 20:", c[:20])
# runs
hits = 0; viol = 0; first = None
for t in range(T + 1 - 9):
    if all(c[t + j] for j in range(9)):
        hits += 1
        if first is None: first = t
        if not (cols[t + 9][1] == 0 and cols[t + 9][2] == 1):
            viol += 1
print("times t with c(t..t+8) all black:", hits, "first:", first, "violations:", viol)
# longest black run
best = cur = 0
for v in c:
    cur = cur + 1 if v else 0
    best = max(best, cur)
print("longest black run in c(0..%d):" % T, best)
# 8-run sharpness on the actual pattern: times with c(t..t+7) black and cell(t+8,1) black
h8 = sum(1 for t in range(T + 1 - 8) if all(c[t + j] for j in range(8)) and cols[t + 8][1] == 1)
print("times with c(t..t+7) black and cell(t+8,1)=1 in the actual pattern:", h8)
