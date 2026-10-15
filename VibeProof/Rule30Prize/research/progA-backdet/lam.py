# Lambda(f): forced left half (row 0) from column 1 = 1 f0 1 f1 ... with column 0 = 0.
# Sideways: C_{k+1}(t) = C_k(t+1) ^ (C_k(t) | C_{k-1}(t)). Use big ints over t: bit t.
import random, sys
def Lambda(f, K):
    # f list of bits, length >= K//2 + 2. returns x0[1..K]
    T = 2 * len(f)
    a = 0
    for s, b in enumerate(f):
        a |= 1 << (2 * s)
        if b: a |= 1 << (2 * s + 1)
    mask = (1 << T) - 1
    prev, cur = 0, a & mask
    out = [cur & 1]
    for k in range(2, K + 1):
        T -= 1
        mask = (1 << T) - 1
        nxt = ((cur >> 1) ^ (cur | prev)) & mask
        prev, cur = cur & mask, nxt
        out.append(cur & 1)
    return out
def randX(n, runs=(1, 2, 4)):
    f = []
    while len(f) < n:
        r = random.choice(runs)
        f += [1] * r + [0]
    return f[:n]
if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    K = 300
    for trial in range(6):
        f = randX(K // 2 + 5)
        x = Lambda(f, K)
        s = ''.join(map(str, x))
        # longest zero run
        import re
        runs = [len(m) for m in re.findall('0+', s)]
        print(s[:150], 'maxzero', max(runs))
    print('random f:')
    for trial in range(3):
        f = [random.getrandbits(1) for _ in range(K // 2 + 5)]
        x = Lambda(f, K); s = ''.join(map(str, x))
        import re
        print(s[:150], 'maxzero', max(len(m) for m in re.findall('0+', s)))
