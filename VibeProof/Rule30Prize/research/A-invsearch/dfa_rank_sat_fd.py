# Pure-SAT CEGAR search for a prefix-regular ranking function (see dfa_rank.py for the specification).
# State: one-hot booleans; transitions T[b][q][r] one-hot rows; accepting F[q].
# Symmetry breaking: BFS canonical numbering (Ulyantsev-Zakirzyanov-Shalyto style parent constraints).
# Pairs found by CEGAR are stored in a file so successive 60-second runs continue.
import sys, random, time, json, os
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch')
from zbl import step
from z3 import Solver, SolverFor, Bool, Or, And, Not, Implies, sat, unsat, PbEq, AtMost, AtLeast, set_param
def G(x): return step(step(x))
def word(x, n, direction):
    W = x.bit_length()
    if direction == 'wall':
        return [(x >> i) & 1 for i in range(W + n + 1)]
    return [(x >> i) & 1 for i in range(W)][::-1]
def rho(dfa, w):
    d0, d1, F = dfa
    q = 0; best = 0 if F[0] else -1
    for k, b in enumerate(w):
        q = d1[q] if b else d0[q]
        if F[q]: best = k + 1
    return best
def finite_ok(dfa, n):
    d0, d1, F = dfa
    for q in range(n):
        c = q
        for i in range(2 * n):
            if i >= n and F[c]: return False
            c = d0[c]
    return True
class Enc:
    def __init__(self, n, direction):
        self.n = n; self.dir = direction
        self.S = SolverFor("QF_FD")
        self.T = [[[Bool(f'T{b}_{q}_{r}') for r in range(n)] for q in range(n)] for b in range(2)]
        self.F = [Bool(f'F{q}') for q in range(n)]
        self.cnt = 0
        for b in range(2):
            for q in range(n):
                self.S.add(PbEq([(v, 1) for v in self.T[b][q]], 1))
        # BFS symmetry breaking: parent p[j][i] (i < j) meaning j first reached from i (by smallest (i, b))
        if n > 1:
            P = [[Bool(f'P{j}_{i}') for i in range(j)] for j in range(n)]
            for j in range(1, n):
                self.S.add(PbEq([(v, 1) for v in P[j]], 1))
                for i in range(j):
                    # p[j]=i  ->  i has a transition to j, and no state k < i has a transition to j
                    self.S.add(Implies(P[j][i], Or(self.T[0][i][j], self.T[1][i][j])))
                    for k in range(i):
                        self.S.add(Implies(P[j][i], And(Not(self.T[0][k][j]), Not(self.T[1][k][j]))))
                    # if from i, symbol 0 goes to j, then (i,0) is the earliest: fine; if only symbol 1 goes, then
                    # symbol 0 from i goes to a state < j
                    self.S.add(Implies(And(P[j][i], Not(self.T[0][i][j])), Or(*[self.T[0][i][k] for k in range(j)])))
                # parents are non-decreasing in j
                if j + 1 < n:
                    for i in range(j):
                        for i2 in range(i):
                            self.S.add(Implies(P[j][i], Not(P[j + 1][i2])))
        # finiteness: zero-orbit from each state, positions n..2n-1 non-accepting
        for q in range(n):
            cur = [q == r for r in range(n)]
            curv = None
            prev = [None] * n
            Z = [[Bool(f'Z{q}_{i}_{r}') for r in range(n)] for i in range(2 * n)]
            for r in range(n):
                self.S.add(Z[0][r] == (r == q))
            for i in range(2 * n - 1):
                for a in range(n):
                    for r in range(n):
                        self.S.add(Implies(And(Z[i][a], self.T[0][a][r]), Z[i + 1][r]))
                        self.S.add(Implies(And(Z[i][a], Not(self.T[0][a][r])), Not(Z[i + 1][r])))
            for i in range(n, 2 * n):
                for r in range(n):
                    self.S.add(Implies(Z[i][r], Not(self.F[r])))
        self.added = set()
    def run_vars(self, w):
        n = self.n; self.cnt += 1; c = self.cnt
        S = [[Bool(f'S{c}_{k}_{r}') for r in range(n)] for k in range(len(w) + 1)]
        A = [Bool(f'A{c}_{k}') for k in range(len(w) + 1)]
        for r in range(n):
            self.S.add(S[0][r] == (r == 0))
        for k, b in enumerate(w):
            for a in range(n):
                for r in range(n):
                    self.S.add(Implies(And(S[k][a], self.T[b][a][r]), S[k + 1][r]))
                    self.S.add(Implies(And(S[k][a], Not(self.T[b][a][r])), Not(S[k + 1][r])))
        for k in range(len(w) + 1):
            for r in range(n):
                self.S.add(Implies(And(S[k][r], self.F[r]), A[k]))
                self.S.add(Implies(And(S[k][r], Not(self.F[r])), Not(A[k])))
        return A
    def add_pair(self, x):
        if x in self.added: return
        self.added.add(x)
        A = self.run_vars(word(x, self.n, self.dir)); B = self.run_vars(word(G(x), self.n, self.dir))
        c = self.cnt
        U = [Bool(f'U{c}_{k}') for k in range(len(A) + 1)]
        self.S.add(Not(U[len(A)]))
        for k in range(len(A)):
            self.S.add(U[k] == Or(A[k], U[k + 1]))
        self.S.add(U[0])
        for kb in range(len(B)):
            self.S.add(Implies(B[kb], U[min(kb + 1, len(A))]))
    def solve(self):
        r = self.S.check()
        if r != sat: return r, None
        m = self.S.model(); n = self.n
        D = [[next(rr for rr in range(n) if m.eval(self.T[b][q][rr], model_completion=True)) for q in range(n)] for b in range(2)]
        FF = [bool(m.eval(self.F[q], model_completion=True)) for q in range(n)]
        return r, (D[0], D[1], FF)
def make_pool(Wmax):
    P = []
    for W in range(1, Wmax + 1):
        for x in range(1 << (W - 1), 1 << W):
            if x & 1 and G(x) & 1: P.append(x)
    extra = []
    for line in open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch/best_mode0.txt'):
        if 'cfg(depth1..W)=' in line:
            cfg = line.split('cfg(depth1..W)=')[1].split()[0]
            x = sum(1 << i for i, ch in enumerate(cfg) if ch == '1')
            while x & 1 and G(x) & 1:
                extra.append(x); x = G(x)
    return P + extra
if __name__ == '__main__':
    n = int(sys.argv[1]); direction = sys.argv[2]; Wp = int(sys.argv[3]); budget = float(sys.argv[4])
    state_file = f'/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/A-invsearch/dfa_pairs_{n}_{direction}.json'
    pairs = json.load(open(state_file)) if os.path.exists(state_file) else []
    P = make_pool(Wp)
    rng = random.Random(len(pairs))
    E = Enc(n, direction)
    if not pairs:
        pairs = rng.sample(P, 30)
    for x in pairs: E.add_pair(x)
    t0 = time.time(); it = 0
    while time.time() - t0 < budget:
        it += 1
        r, dfa = E.solve()
        if r == unsat:
            print(f'n={n} dir={direction}: UNSAT with {len(E.added)} pairs (iter {it}, {time.time()-t0:.1f}s)')
            json.dump(sorted(E.added), open(state_file, 'w'))
            sys.exit(0)
        assert finite_ok(dfa, n)
        viol = [x for x in P if not (rho(dfa, word(G(x), n, direction)) < rho(dfa, word(x, n, direction)))]
        if not viol:
            print(f'n={n} dir={direction}: CANDIDATE passing pool ({len(P)}): {dfa}')
            json.dump(sorted(E.added), open(state_file, 'w'))
            sys.exit(0)
        rng.shuffle(viol)
        # prefer short violating configurations
        viol.sort(key=lambda x: x.bit_length())
        for x in viol[:5] + viol[5:][:5]: E.add_pair(x)
    print(f'n={n} dir={direction}: undecided after {it} iterations, {len(E.added)} pairs ({time.time()-t0:.1f}s)')
    json.dump(sorted(E.added), open(state_file, 'w'))
