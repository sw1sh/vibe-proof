def step(x): return (x >> 1) ^ (x | (x << 1))
for K in range(1, 9):
    x = 1 << (K - 1); s = ''
    for t in range(120):
        s += str(x & 1); x = step(x)
    print(K, s)
