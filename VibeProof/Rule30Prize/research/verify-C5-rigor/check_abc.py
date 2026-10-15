# Exhaustive forward simulation of actual rule 30 from EVERY row window at time t
# (columns -K..K), shrinking the light cone each step. Any actual configuration's
# restriction to that window is one of these rows, so universally verified relations
# hold in the true pattern. Checks C5 (a), (b), (c) and the short (d) exclusions.
import itertools

def rule(l, c, r):
    return l ^ (c | r)

def evolve(row, lo, steps):
    """row: dict col->val for cols lo..lo+len-1. Returns list of dicts for times 0..steps."""
    hist = [dict(row)]
    cur = dict(row)
    for _ in range(steps):
        cols = sorted(cur)
        new = {}
        for p in cols[1:-1]:
            new[p] = rule(cur[p - 1], cur[p], cur[p + 1])
        hist.append(new)
        cur = new
    return hist

def run(K, steps, check):
    n = 2 * K + 1
    cnt_cond = 0
    bad = 0
    for bits in itertools.product((0, 1), repeat=n):
        row = {p: bits[p + K] for p in range(-K, K + 1)}
        h = evolve(row, -K, steps)
        r = check(h)
        if r is None:
            continue
        cnt_cond += 1
        if not r:
            bad += 1
    return cnt_cond, bad

def c(h, k): return h[k][0]
def cell(h, k, p): return h[k][p]

# (a) c(s)=1, c(s+1)=0  =>  cell(s,-1)=1
def chk_a(h):
    if not (c(h, 0) == 1 and c(h, 1) == 0): return None
    return cell(h, 0, -1) == 1

# (b) c(t..t+4) = 0,1,0,1,0  =>  cell(t,-4) = 0
def chk_b(h):
    if [c(h, k) for k in range(5)] != [0, 1, 0, 1, 0]: return None
    return cell(h, 0, -4) == 0

# (c) c(t..t+5) = 0,1,0,1,0,1  =>  the four relations
def chk_c(h):
    if [c(h, k) for k in range(6)] != [0, 1, 0, 1, 0, 1]: return None
    b = lambda k: cell(h, k, 1)
    return (cell(h, 0, -2) == b(0) and cell(h, 1, -2) == b(2)
            and cell(h, 0, -3) == 1 - b(2) and cell(h, 1, -3) == 1 - b(2)
            and cell(h, 1, -4) == b(4))

# (d) short exclusions with 8 alternating values: 10 pair, AA, BB, BC, CC, ABAB
def chk_d(h):
    if [c(h, k) for k in range(8)] != [k % 2 for k in range(8)]: return None
    b = [cell(h, k, 1) for k in range(8)]
    pairs = [(b[2 * j], b[2 * j + 1]) for j in range(4)]
    if (1, 0) in pairs: return False
    name = {(0, 0): 'A', (0, 1): 'B', (1, 1): 'C'}
    s = ''.join(name[p] for p in pairs)
    return not any(x in s for x in ['AA', 'BB', 'BC', 'CC', 'ABAB'])

# (e) zeros of column -1 at times in the alternating range are exactly c=0 times with b=1
def chk_e(h):
    if [c(h, k) for k in range(8)] != [k % 2 for k in range(8)]: return None
    for k in range(7):  # need c(k+1) known
        a = cell(h, k, -1)
        if c(h, k) == 1 and a != 1: return False
        if c(h, k) == 0 and a != 1 - cell(h, k, 1): return False
    return True

# light cones: (a) needs cols -2..2 for 1 step; (b) c(t+4) needs -4..4, cell(t,-4) fine;
# (c) c(t+5) needs -5..5, cell(t+4,1) needs -3..5, cell(t+1,-4) needs -5..-3;
# (d),(e) c(t+7) needs -7..7, cell(t+7,1) needs -6..8 -> use K=8 (17 cells).
for name, K, steps, f in [('a', 3, 1, chk_a), ('b', 6, 4, chk_b), ('c', 7, 5, chk_c)]:
    n, bad = run(K, steps, f)
    print(f'({name}) K={K}: rows satisfying hypothesis = {n}, violations = {bad}')
