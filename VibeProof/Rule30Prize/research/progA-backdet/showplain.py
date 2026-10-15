import sys
def step(x): return (x >> 1) ^ (x | (x << 1))
s = sys.argv[1]; T = int(sys.argv[2]); every = int(sys.argv[3]) if len(sys.argv) > 3 else 1
x = 0
for i, ch in enumerate(s):
    if ch == '1': x |= 1 << i
K = len(s); width = min(K + T + 1, 150)
for t in range(T + 1):
    if t % every == 0:
        row = ''.join('#' if (x >> (k - 1)) & 1 else '.' for k in range(width, 0, -1))
        print('%3d %s|' % (t, row))
    x = step(x)
