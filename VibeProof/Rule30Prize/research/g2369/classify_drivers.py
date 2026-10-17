# Which frozen-boundary steps (alpha, beta, gamma) with edge state (x0, x1) have driver patterns
# (A, B) = (x1|x0, x1) that occur inside Phi-orbits of finite seeds at some depth j
# (edge = bits j-2, j-1; bulk = bits >= j)?
import itertools
def Phi(x): return x ^ ((2 * x) | (4 * x))
def bdry(al, be, ga, y):
    return y ^ (al + 2 * (be if y % 2 == 0 else ga))
def step(al, be, ga, x): return bdry(al, be, ga, Phi(x))
T = 64
def drivers_step(al, be, ga, x0, x1):
    x, out = x0 + 2 * x1, []
    for t in range(T):
        e0, e1 = x & 1, (x >> 1) & 1
        out.append((e1 | e0, e1))
        x = step(al, be, ga, x) & 3          # the edge evolves autonomously
    return tuple(out)
realizable = {}
for j in range(2, 11):
    M = (1 << j) - 1
    for v in range(1 << j):
        x, out = v, []
        for t in range(T):
            r1, r2 = (x >> (j - 1)) & 1, (x >> (j - 2)) & 1
            out.append((r1 | r2, r1))
            x = Phi(x) & M                    # low j bits evolve autonomously
        realizable.setdefault(tuple(out), (j, v))
names = {(0,0,0): 'c=Phi', (1,0,0): 'b', (1,1,0): 'a'}
new = []
for al, be, ga in itertools.product((0, 1), repeat=3):
    for x0, x1 in itertools.product((0, 1), repeat=2):
        d = drivers_step(al, be, ga, x0, x1)
        hit = realizable.get(d)
        h = (be, 1 ^ ga)   # h(0), h(1)
        tag = names.get((al, be, ga), '')
        print(f'step ({al},{be},{ga}) {tag:6s} h=(h0,h1)={h} edge=({x0},{x1})  A,B period-4 pattern '
              f'{"".join(str(p[0]) for p in d[:4])},{"".join(str(p[1]) for p in d[:4])}  ->',
              f'depth {hit[0]}, low bits {hit[1]:0{hit[0]}b}' if hit else 'NEW (no finite-seed match, j <= 10)')
        if not hit: new.append((al, be, ga, x0, x1))
print('new cases:', new)
