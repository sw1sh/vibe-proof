import sys
sys.path.insert(0, '.')
from hist import run
# print walls: position k is a wall if x_k == x_{k-1} (x_0 = 0). Mark class 0 (k+t even) as 'O'/'o' (00-wall/11-wall), class 1 as 'X'/'x'
L = [int(c) for c in sys.argv[1]]
rows, D = run(L)
N = len(rows[-1]) + 1
for t, x in enumerate(rows):
    xx = [0] + x + [0]
    s = []
    for k in range(1, len(xx)):
        if xx[k] == xx[k-1]:
            cls = (k + t) % 2
            typ00 = (xx[k] == 0)
            s.append(('O' if typ00 else 'o') if cls == 0 else ('X' if typ00 else 'x'))
        else:
            s.append('.')
    print(f"{t:3d} " + ''.join(reversed(s)).rjust(N))
