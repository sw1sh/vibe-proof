import sys
def step(x): return (x >> 1) ^ (x | (x << 1))
s = sys.argv[1]  # x0 as string k=1..
T = int(sys.argv[2])
x = 0
for i, ch in enumerate(s):
    if ch == '1': x |= 1 << i
K = len(s)
width = K + T + 1
for t in range(T + 1):
    row = ''.join('#' if (x >> (k - 1)) & 1 else '.' for k in range(width, 0, -1))
    mark = '' if t % 2 else ('  ok' if x & 1 else '  DEATH')
    print('%3d %s|%s' % (t, row, mark))
    if t % 2 == 0 and not (x & 1): break
    x = step(x)
