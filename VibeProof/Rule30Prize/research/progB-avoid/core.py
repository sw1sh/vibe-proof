"""Analyse the unique bad SCC B_b of the strip graph (word w, width b), dumped by scc_an.
Computes: forced nodes, the maximal input-closed subset K of B (every input keeps you in K),
SCCs of B minus forced nodes, and whether those are bad (output inconsistent).
usage: python3 -I core.py w b dumpfile
"""
import sys
from collections import deque, defaultdict

w = sys.argv[1]; b = int(sys.argv[2]); fn = sys.argv[3]
P = len(w)
B = set()
for line in open(fn):
    ph, s, c = map(int, line.split())
    B.add((ph, s))


def succ2(ph, s):
    c = int(w[ph])
    bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
    base = 0
    for p in range(1, b):
        base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nph = (ph + 1) % P
    if bit(b):
        v = base | ((1 ^ bit(b - 1)) << (b - 1))
        return [(nph, v), (nph, v)]
    return [(nph, base | (bit(b - 1) << (b - 1))), (nph, base | ((1 ^ bit(b - 1)) << (b - 1)))]


S = {v: succ2(*v) for v in B}
forced = {}
for v in B:
    a, c = S[v]
    if a != c:
        ia, ic = a in B, c in B
        if ia != ic:
            forced[v] = 0 if ia else 1
print(f"w={w} b={b} |B|={len(B)} forced={len(forced)}")

# maximal input-closed subset
K = set(B)
changed = True
while changed:
    changed = False
    rm = [v for v in K if not (S[v][0] in K and S[v][1] in K)]
    if rm:
        changed = True
        for v in rm:
            K.discard(v)
print(f"  maximal input-closed subset K: {len(K)}")


def sccs(nodes, edges):
    # iterative Tarjan
    index = {}; low = {}; onst = set(); st = []; res = []; cnt = 0
    for root in nodes:
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            v, i = work[-1]
            if i == 0 and v not in index:
                index[v] = low[v] = cnt; cnt += 1; st.append(v); onst.add(v)
            es = [u for u in edges(v) if u in nodes]
            pushed = False
            while i < len(es):
                u = es[i]; i += 1
                if u not in index:
                    work[-1] = (v, i); work.append((u, 0)); pushed = True; break
                elif u in onst:
                    low[v] = min(low[v], index[u])
            if pushed:
                continue
            work[-1] = (v, i)
            if low[v] == index[v]:
                comp = []
                while True:
                    u = st.pop(); onst.discard(u); comp.append(u)
                    if u == v:
                        break
                res.append(comp)
            work.pop()
            if work:
                pv = work[-1][0]; low[pv] = min(low[pv], low[v])
    return res


def is_bad(comp, edges):
    cs = set(comp)
    nontriv = len(comp) > 1 or any(u == comp[0] for u in edges(comp[0]))
    if not nontriv:
        return None
    st = comp[0]
    # find a cycle through st
    par = {st: None}; dq = deque([st]); back = None
    while dq and back is None:
        x = dq.popleft()
        for y in edges(x):
            if y not in cs:
                continue
            if y == st:
                back = x; break
            if y not in par:
                par[y] = x; dq.append(y)
    path = []
    x = back
    while x is not None:
        path.append(x); x = par[x]
    path.reverse()
    word = [x[1] & 1 for x in path if w[x[0]] == '0']
    L = len(word)
    m = next(d for d in range(1, L + 1) if L % d == 0 and all(word[i] == word[i - d] for i in range(d, L))) if L else 1
    if L == 0:
        word = [0]; m = 1
    pos = {st: 0}; dq = deque([st])
    while dq:
        x = dq.popleft()
        if w[x[0]] == '0':
            if (x[1] & 1) != word[pos[x] % m]:
                return True
            np = (pos[x] + 1) % m
        else:
            np = pos[x]
        for y in edges(x):
            if y not in cs:
                continue
            if y in pos:
                if pos[y] != np:
                    return True
            else:
                pos[y] = np; dq.append(y)
    return False


def edgesB(v):
    a, c = S[v]
    return [a] if a == c else [a, c]


if K:
    cK = sccs(K, edgesB)
    for comp in cK:
        bad = is_bad(comp, edgesB)
        if bad is not None:
            print(f"  K-SCC size {len(comp)} bad={bad}")
# SCCs of B \ forced
Bf = B - set(forced)
cF = sccs(Bf, edgesB)
nb = 0
for comp in cF:
    bad = is_bad(comp, edgesB)
    if bad:
        nb += 1
        print(f"  (B minus forced)-SCC size {len(comp)} bad")
print(f"  bad SCCs avoiding all forced nodes: {nb}")
