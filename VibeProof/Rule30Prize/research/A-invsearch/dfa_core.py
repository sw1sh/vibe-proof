# Find a small set of surviving pairs that is UNSAT for every DFA with n states (prefix-ranking from the wall),
# by deletion-based core minimisation.
import sys, random
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import step
from z3 import Solver, EnumSort, Function, BoolSort, Or, Not, Implies, unsat
def G(x): return step(step(x))
def word(x, n): W = x.bit_length(); return [(x >> i) & 1 for i in range(W + n + 1)]
def is_unsat(n, pairs):
    Q, qs = EnumSort(f'Q{n}_{random.random()}', [f'q{i}_{random.random()}' for i in range(n)])
    d0 = Function('d0', Q, Q); d1 = Function('d1', Q, Q); F = Function('F', Q, BoolSort())
    S = Solver()
    for q in qs:
        cur = q
        for i in range(2 * n):
            if i >= n: S.add(Not(F(cur)))
            cur = d0(cur)
    def accs(w):
        cur = qs[0]; out = [F(cur)]
        for b in w:
            cur = d1(cur) if b else d0(cur)
            out.append(F(cur))
        return out
    for x in pairs:
        A = accs(word(x, n)); B = accs(word(G(x), n))
        S.add(Or(*A))
        for kb, ab in enumerate(B):
            later = [A[k] for k in range(kb + 1, len(A))]
            S.add(Implies(ab, Or(*later)) if later else Not(ab))
    return S.check() == unsat
n = int(sys.argv[1])
P = []
for W in range(1, 11):
    for x in range(1 << (W - 1), 1 << W):
        if x & 1 and G(x) & 1: P.append(x)
random.seed(1); random.shuffle(P)
core = P[:60]
assert is_unsat(n, core), 'initial set not unsat'
i = 0
while i < len(core):
    trial = core[:i] + core[i + 1:]
    if is_unsat(n, trial): core = trial
    else: i += 1
print(f'n={n}: minimal UNSAT core of {len(core)} pairs:')
for x in core:
    print('  x =', ''.join(map(str, word(x, 0)[:x.bit_length()])), ' G(x) =', ''.join(map(str, word(G(x), 0)[:G(x).bit_length()])))
