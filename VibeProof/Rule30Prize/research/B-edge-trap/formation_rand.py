import sys, random
# Like formation.py but with a random initial right half of width L (effectively infinite), driver w^inf from phase ph0.
w = sys.argv[1]; L = int(sys.argv[2]); seed = int(sys.argv[3]); ph0 = int(sys.argv[4]); S = int(sys.argv[5])
K = int(sys.argv[6]); Q = int(sys.argv[7]); every = int(sys.argv[8])
P = len(w)
random.seed(seed)
row = (random.getrandbits(L) << 1) | int(w[ph0])
rows = []
for t in range(S):
    rows.append(row)
    Wd = row.bit_length() + 2
    mask = (1 << Wd) - 1
    row = (((row << 1) ^ (row | (row >> 1))) & mask) & ~1 | int(w[(ph0 + t + 1) % P])
fin = {}
for t in range(S - 4 * Q, S):
    fin.setdefault((ph0 + t) % Q, rows[t] >> 1)
def agree(t):
    x = (rows[t] >> 1) ^ fin[(ph0 + t) % Q]
    k = 0
    while k < K and not (x >> k) & 1: k += 1
    return k
line = [min(agree(t) for t in range(t0, t0 + Q)) for t0 in range(0, S - Q, Q)]
for i in range(0, len(line), every):
    print('t=%6d  %s' % (i * Q, ' '.join('%2d' % x for x in line[i:i + every])))
