# Image languages of the w-driven right half of rule 30.
# L_n = set of prefixes (columns 1..l) of configurations reachable at time n from ALL configurations
# (driver c(t) = w[t mod |w|], starting at phase 0). Represented by minimal DFAs (prefix-closed).
import sys

class DFA:
    # states 0..n-1; trans[q] = (t0, t1) with -1 for dead; start = 0; all live states accepting
    def __init__(self, trans):
        self.trans = trans
    def size(self): return len(self.trans)

def full():
    return DFA([(0, 0)])

def image(D, c):
    # subset construction on NFA states (q, xa, xb)
    T = D.trans
    def step2(q, b):
        return T[q][b] if q >= 0 else -1
    # initial subsets after reading y1
    start_succ = {0: set(), 1: set()}
    for x1 in (0, 1):
        q1 = step2(0, x1)
        if q1 < 0: continue
        for x2 in (0, 1):
            q2 = step2(q1, x2)
            if q2 < 0: continue
            y1 = c ^ (x1 | x2)
            start_succ[y1].add((q2, x1, x2))
    # DFA states: frozensets; special start
    idx = {}; trans = []; queue = []
    def get(S):
        S = frozenset(S)
        if not S: return -1
        if S not in idx:
            idx[S] = len(trans); trans.append(None); queue.append(S)
        return idx[S]
    trans.append(None)  # start = 0
    s0 = get(start_succ[0]); s1 = get(start_succ[1])
    trans[0] = (s0, s1)
    qi = 0
    while qi < len(queue):
        S = queue[qi]; qi += 1
        nxt = {0: set(), 1: set()}
        for (q, xa, xb) in S:
            for xn in (0, 1):
                q2 = T[q][xn]
                if q2 < 0: continue
                y = xa ^ (xb | xn)
                nxt[y].add((q2, xb, xn))
        trans[idx[S]] = (get(nxt[0]), get(nxt[1]))
    return minimize(DFA(trans))

def minimize(D):
    T = D.trans; n = len(T)
    # all states live (we only create nonempty subsets) -> but some live states may have no infinite extension?
    # (cannot happen: every state has at least one successor by extendability). Moore partition refinement.
    part = [0] * n
    while True:
        sig = {}
        newpart = [0] * n
        for q in range(n):
            a, b = T[q]
            key = (part[q], part[a] if a >= 0 else -1, part[b] if b >= 0 else -1)
            if key not in sig: sig[key] = len(sig)
            newpart[q] = sig[key]
        if len(sig) == len(set(part)):
            part = newpart; break
        part = newpart
    # build quotient with start state 0 mapped to 0
    order = {}; 
    ren = {}
    ren[part[0]] = 0
    for q in range(n):
        if part[q] not in ren: ren[part[q]] = len(ren)
    trans = [None] * len(ren)
    for q in range(n):
        a, b = T[q]
        trans[ren[part[q]]] = (ren[part[a]] if a >= 0 else -1, ren[part[b]] if b >= 0 else -1)
    return DFA(trans)

def prefixes(D, l):
    # all accepted words of length l
    res = []
    def rec(q, s):
        if len(s) == l: res.append(s); return
        for b in (0, 1):
            q2 = D.trans[q][b]
            if q2 >= 0: rec(q2, s + str(b))
    rec(0, '')
    return res

def first_letters(D):
    return [b for b in (0, 1) if D.trans[0][b] >= 0]

if __name__ == '__main__':
    w = sys.argv[1]; nmax = int(sys.argv[2])
    wb = [int(ch) for ch in w]; P = len(wb)
    D = full()
    for n in range(1, nmax + 1):
        D = image(D, wb[(n - 1) % P])
        print(n, "phase", n % P, "DFA size", D.size(), "first letters", first_letters(D), flush=True)
