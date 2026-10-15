def step(x): return (x >> 1) ^ (x | (x << 1))
def survive_W(x, maxt):
    t = 0
    while t < maxt:
        if (x & 3) == 0: return t
        x = step(x); t += 1
    return None
import sys
W = int(sys.argv[1])
best = {}
arg = {}
for x in range(1, 1 << W):
    d = survive_W(x, 20*W+100)
    K = x.bit_length()
    if d is None: d = 10**9
    if d > best.get(K, -1):
        best[K] = d; arg[K] = x
print([(K, best[K]) for K in sorted(best)])
print({K: bin(arg[K])[2:][::-1] for K in sorted(arg)})
