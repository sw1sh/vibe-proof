import sys
# simulate ZBL from finite L (list x_1..x_W), return list of rows (each list x_1..x_{W+t}) until death (inclusive)
def step(x):
    n = len(x) + 1
    xx = [0] + x + [0, 0]
    return [xx[k+1] ^ (xx[k] | xx[k-1]) for k in range(1, n+1)]
def run(L, maxT=400):
    rows = [list(L)]
    t = 0
    while True:
        x = rows[-1]
        if t % 2 == 0 and x[0] == 0: return rows, t
        if t >= maxT: return rows, None
        rows.append(step(x)); t += 1
def firstdef(x):
    for k in range(1, len(x)+3):
        v = x[k-1] if k <= len(x) else 0
        if v != (k % 2): return k
def walls(x):
    xx = [0] + x + [0]
    return [k for k in range(1, len(xx)) if xx[k] == xx[k-1]]
if __name__ == '__main__':
    L = [int(c) for c in sys.argv[1]]
    rows, D = run(L)
    f = ''.join(str(rows[t][0]) for t in range(1, len(rows), 2))
    print('D =', D, ' f =', f)
    for t, x in enumerate(rows):
        print(t, 'firstdef', firstdef(x), 'width', len(x), 'nwalls_in_cone', len([k for k in walls(x) if k <= len(x)]), 'weight', sum(x))
