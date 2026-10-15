import sys, random
sys.path.insert(0, '.')
from sim import *
w = '0001'
random.seed(1)
P = 4
x = int('111011101100100111010010100001', 2); ph = 0
hist = run(x, w, ph, 20000)
# extent of 8-periodicity over windows
for start in [1000, 3000, 6000, 10000, 15000]:
    k = 0
    while k < 400:
        mask = (1 << (k + 1)) - 1
        if all((hist[t][1] & mask) == (hist[t + 8][1] & mask) for t in range(start, start + 2000)): k += 1
        else: break
    print("window", start, "columns 1..%d have period 8" % k)
# print the periodic layer over one period (columns 1..30)
for t in range(16000, 16016):
    print(hist[t][0], cols(hist[t][1], 1, 40))
