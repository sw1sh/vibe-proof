# CEGAR search for a prefix-regular ranking function for the constrained ZBL.
# rho_A(x) = max { k >= 0 : A accepts x[1..k] }  (x read from the wall; -1 if none), where x is the finite
# configuration followed by zeros.  Requirements:
#   (C1) every 0-cycle of A is non-accepting  (so rho_A(x) <= width + n for finite x);
#   (C2) for every finite x with x_1 = 1 and G(x)_1 = 1 (a surviving double step): rho_A(G(x)) < rho_A(x).
# If (C1),(C2) hold, every constrained run from x lasts at most rho_A(x)+1 double steps.
# UNSAT on a finite set of genuine surviving pairs proves that no DFA with n states works.
# direction 'wall' reads depths 1,2,...; 'edge' reads from the deepest black cell towards the wall.
import sys, random, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import step
from z3 import Solver, EnumSort, Function, BoolSort, Or, And, Not, Implies, sat, unsat, Bool, BoolVal
def G(x): return step(step(x))
def bits(x, L): return [(x >> i) & 1 for i in range(L)]
def word(x, n, direction):
    W = x.bit_length()
    if direction == 'wall':
        return bits(x, W + n + 1)
    else:
        b = bits(x, W)[::-1]           # from the edge to the wall
        return b
def pool(Wmax):
    P = []
    for W in range(1, Wmax + 1):
        for x in range(1 << (W - 1), 1 << W):
            if x & 1 and G(x) & 1:
                P.append(x)
    return P
def rho(dfa, w):
    d0, d1, F = dfa
    q = 0; best = 0 if F[0] else -1
    for k, b in enumerate(w):
        q = d1[q] if b else d0[q]
        if F[q]: best = k + 1
    return best
def search(n, direction, Wpool, seed=0, max_iter=400, init=40, verbose=True):
    rng = random.Random(seed)
    P = pool(Wpool)
    # add long-surviving configurations (from the exhaustive search) and their surviving iterates
    extra = []
    for line in open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch/best_mode0.txt'):
        if 'cfg(depth1..W)=' in line:
            c = line.split('cfg(depth1..W)=')[1].split()[0]
            x = sum(1 << i for i, ch in enumerate(c) if ch == '1')
            while x & 1 and G(x) & 1:
                extra.append(x); x = G(x)
    P = P + extra
    Q, qs = EnumSort('Q', [f'q{i}' for i in range(n)])
    d0 = Function('d0', Q, Q); d1 = Function('d1', Q, Q); F = Function('F', Q, BoolSort())
    S = Solver()
    # (C1): zero-orbit from every state: after n zeros, the next n states are non-accepting
    for q in qs:
        cur = q
        for i in range(2 * n):
            if i >= n: S.add(Not(F(cur)))
            cur = d0(cur)
    added = set()
    def add_pair(x):
        if x in added: return
        added.add(x)
        for (xx, tag) in ((x, 'a'), (G(x), 'b')):
            pass
        wa = word(x, n, direction); wb = word(G(x), n, direction)
        def accs(w):
            cur = qs[0]; out = [F(cur)]
            for b in w:
                cur = d1(cur) if b else d0(cur)
                out.append(F(cur))
            return out
        A = accs(wa); B = accs(wb)
        # rho(Gx) < rho(x): every accepted position of B is below some accepted position of A; and A accepts something
        S.add(Or(*A))
        for kb, ab in enumerate(B):
            later = [A[k] for k in range(kb + 1, len(A))]
            S.add(Implies(ab, Or(*later)) if later else Not(ab))
    order = list(range(len(P))); rng.shuffle(order)
    for i in order[:init]: add_pair(P[i])
    it = 0; t0 = time.time()
    while it < max_iter:
        it += 1
        r = S.check()
        if r == unsat:
            if verbose: print(f'n={n} dir={direction}: UNSAT after {it} iterations with {len(added)} pairs ({time.time()-t0:.1f}s)')
            return ('unsat', sorted(added))
        m = S.model()
        dd0 = [qs.index(m.eval(d0(q), model_completion=True)) if False else None for q in qs]
        # decode
        def idx(v):
            for j, q in enumerate(qs):
                if m.eval(v == q, model_completion=True): return j
        D0 = [idx(d0(q)) for q in qs]; D1 = [idx(d1(q)) for q in qs]
        FF = [bool(m.eval(F(q), model_completion=True)) for q in qs]
        dfa = (D0, D1, FF)
        viol = [x for x in P if not (rho(dfa, word(G(x), n, direction)) < rho(dfa, word(x, n, direction)))]
        if not viol:
            if verbose: print(f'n={n} dir={direction}: candidate passes pool of {len(P)} pairs: d0={D0} d1={D1} F={FF}')
            return ('candidate', dfa)
        rng.shuffle(viol)
        for x in viol[:20]: add_pair(x)
    if verbose: print(f'n={n} dir={direction}: undecided after {max_iter} iterations ({len(added)} pairs)')
    return ('undecided', None)
if __name__ == '__main__':
    n = int(sys.argv[1]); direction = sys.argv[2]; Wp = int(sys.argv[3])
    search(n, direction, Wp, max_iter=int(sys.argv[4]) if len(sys.argv) > 4 else 200)
