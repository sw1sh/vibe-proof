import sys
# ZBL, k-coords; print rows with wall on the right (p-orientation): ... x_3 x_2 x_1 | 0
def run(L, T):
    x = list(L)
    rows = []
    for t in range(T+1):
        rows.append(x[:])
        n = len(x) + 1
        xx = [0] + x + [0, 0]  # xx[k] = x_k, xx[0] = 0
        x = [xx[k+1] ^ (xx[k] | xx[k-1]) for k in range(1, n+1)]
    return rows
L = [int(c) for c in sys.argv[1]]
T = int(sys.argv[2])
rows = run(L, T)
N = len(rows[-1])
for t, r in enumerate(rows):
    s = ''.join('#' if v else '.' for v in reversed(r))
    mark = ' *' if t % 2 == 0 else '  '
    ok = '' if (t % 2 == 1 or r[0] == 1) else '  <-- DEATH'
    print(f"{t:3d}{mark} " + s.rjust(N) + '|' + ok)
