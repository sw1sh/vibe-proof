# Check Jen's Lemma claim "period of inner columns divides lcm(p_i,p_j)" on a finite IC.
def step(rule, cells, lo, hi):
    new = {}
    for p in range(lo - 1, hi + 2):
        l = cells.get(p - 1, 0); c = cells.get(p, 0); r = cells.get(p + 1, 0)
        new[p] = (rule >> (4 * l + 2 * c + r)) & 1
    return new, lo - 1, hi + 1

def run(rule, init, T):
    cells = dict(init); lo = min(init); hi = max(init)
    hist = [dict(cells)]
    for _ in range(T):
        cells, lo, hi = step(rule, cells, lo, hi)
        hist.append(dict(cells))
    return hist

# rule 108 blinker 101 <-> 111 at positions 0,1,2
hist = run(108, {0: 1, 1: 0, 2: 1}, 12)
for p in range(-1, 4):
    print('rule108 column', p, [h.get(p, 0) for h in hist])
