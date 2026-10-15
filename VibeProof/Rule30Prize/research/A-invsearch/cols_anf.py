# Columns of a surviving run as sliding block codes of g = not f  (y = column -1 = (1, f0, 1, f1, ...)).
# x_{2s}(-k) = E_k(g_s, g_{s+1}, ...), x_{2s+1}(-k) = O_k(g_s, ...).  Print ANF in g (shift-invariant, so s = 0).
import sys
n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
K = int(sys.argv[2]) if len(sys.argv) > 2 else 12
golden = len(sys.argv) > 3 and sys.argv[3] == 'golden'
N = 1 << n
FULL = (1 << N) - 1
G = []
for i in range(n):
    tt = 0
    for a in range(N):
        if (a >> i) & 1: tt |= 1 << a
    G.append(tt)
T = 2 * n
y = [FULL if t % 2 == 0 else FULL ^ G[t // 2] for t in range(T)]   # f = not g
cols = [[0] * T, y]
for k in range(2, K + 1):
    cur, prev = cols[-1], cols[-2]
    cols.append([cur[t + 1] ^ (cur[t] | prev[t]) for t in range(len(cur) - 1)])
# golden mean on f (no two consecutive f = 0) == no two consecutive g = 1: restrict the domain
valid = FULL
if golden:
    valid = 0
    for a in range(N):
        if all(not ((a >> i) & 1 and (a >> (i + 1)) & 1) for i in range(n - 1)): valid |= 1 << a
def anf(tt):
    c = [(tt >> a) & 1 for a in range(N)]
    for i in range(n):
        for a in range(N):
            if (a >> i) & 1: c[a] ^= c[a ^ (1 << i)]
    return [a for a in range(N) if c[a]]
def mono(a):
    return '1' if a == 0 else ''.join(f'g{i}' for i in range(n) if (a >> i) & 1)
def show(tt):
    if golden:
        # print as a function on the valid set: report support pattern instead of ANF
        on = [a for a in range(N) if (valid >> a) & 1 and (tt >> a) & 1]
        tot = bin(valid).count('1')
        return f'{len(on)}/{tot} ones'
    ms = anf(tt)
    s = ' + '.join(mono(a) for a in ms[:14]) + (' + ...' if len(ms) > 14 else '')
    return s if ms else '0'
for k in range(1, K + 1):
    if len(cols[k]) < 2: break
    print(f'col -{k}: even: {show(cols[k][0])}   |   odd: {show(cols[k][1])}')
