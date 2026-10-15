import sys
# print (driver phase, strip state of columns k+1..k+b as int with bit i = column k+1+i) at time n+S for a run
w = sys.argv[1]; n = int(sys.argv[2]); d = int(sys.argv[3]); ph0 = int(sys.argv[4]); S = int(sys.argv[5]); k = int(sys.argv[6]); b = int(sys.argv[7])
P = len(w)
def drv(t): return (d >> t) & 1 if t < n else int(w[(ph0 + t - n) % P])
row = drv(0)
for t in range(n + S):
    Wd = row.bit_length() + 2; mask = (1 << Wd) - 1
    row = (((row << 1) ^ (row | (row >> 1))) & mask) & ~1 | drv(t + 1)
t = n + S
ph = (ph0 + t - n) % P
print(ph, (row >> (k + 1)) & ((1 << b) - 1))
