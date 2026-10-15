import sys
sys.path.insert(0, '.')
from sim import *
import closure as C
w = '0001'
lines = [l for l in open('surv_0001.txt') if l.startswith('SURV')]
parts = lines[0].split(); cfg = parts[2]; ph0 = int(parts[4])
x = sum(1 << i for i, ch in enumerate(cfg) if ch == '1')
hist = run(x, w, ph0, 6100)
for t in range(6000, 6016):
    print(hist[t][0], cols(hist[t][1], 1, 30))
# columns' periods
for p in range(1, 26):
    seq = [(hist[t][1] >> (p - 1)) & 1 for t in range(5000, 6000)]
    per = next((d for d in range(1, 300) if all(seq[i] == seq[i + d] for i in range(len(seq) - d))), None)
    print("col", p, "period", per, ''.join(map(str, seq[:16])) if per and per <= 16 else '')
C.BW = 23
start = (hist[6000][0], hist[6000][1] & ((1 << 23) - 1))
cl = C.closure(w, 23, start)
print(len(cl))
# skeleton of the closure
for ph in range(4):
    S = [s for (q, s) in cl if q == ph]
    row = ''
    for p in range(1, 24):
        vals = set((s >> (p - 1)) & 1 for s in S)
        row += str(vals.pop()) if len(vals) == 1 else '*'
    print(ph, row, len(S))
# compare with S_w trap at b=16
T = [tuple(map(int, l.split()[:2])) for l in open('../newideas/trap_0001_16.txt').read().strip().split('\n')[1:]]
for ph in range(4):
    S = [s for (q, s) in T if q == ph]
    row = ''
    for p in range(1, 17):
        vals = set((s >> (p - 1)) & 1 for s in S)
        row += str(vals.pop()) if len(vals) == 1 else '*'
    print('Sw', ph, row, len(S))
