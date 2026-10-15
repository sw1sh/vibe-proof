# Independent re-implementation (written from the statements only) of the finite
# relaxation checks behind placego entries 38/40/41 (and cochon123's strip claim).
# Rule 30: x'(k) = x(k-1) XOR (x(k) OR x(k+1)).
import sys, itertools
sys.setrecursionlimit(10000)

# ---------- one-sided relaxation: cells x1..xK right of column 0, free bit beyond xK
def one_sided_step_set(states, c, K):
    mask = (1 << K) - 1
    out = set()
    for x in states:
        base = (((x << 1) | c) ^ (x | (x >> 1))) & mask   # bit j <-> x_{j+1}; x_{K+1} treated as 0 here
        out.add(base)
        # free bit z=1 enters the OR at the last cell: x_K' = x_{K-1} xor (x_K or z)
        lastbit = 1 << (K - 1)
        x_km1 = (x >> (K - 2)) & 1 if K >= 2 else c
        z1 = (base & ~lastbit) | ((x_km1 ^ 1) << (K - 1))
        out.add(z1)
    return out

def one_sided_determined(word, K):
    p = len(word)
    S = set(range(1 << K))
    for it in range(10000):
        cur = S
        for j in range(p):
            cur = one_sided_step_set(cur, word[j], K)
        if cur == S:
            break
        if not cur <= S:
            raise RuntimeError("non-monotone")
        S = cur
    # tick sets
    R = S
    vals = []
    for j in range(p):
        bits = {x & 1 for x in R}
        if len(bits) != 1:
            return False, None, len(S)
        vals.append(bits.pop())
        R = one_sided_step_set(R, word[j], K)
    assert R == S
    return True, ''.join(map(str, vals)), len(S)

# ---------- two-sided strip: cells -r..r, interior -(r-1)..(r-1) updated, outer two free
def two_sided_graph(word, r):
    n = 2 * r + 1
    full = (1 << n) - 1
    inner = full & ~1 & ~(1 << (n - 1))
    cbit = r  # bit index of cell 0
    p = len(word)
    def succ(row, ph):
        nph = (ph + 1) % p
        base = ((row << 1) ^ (row | (row >> 1))) & inner
        res = []
        if ((base >> cbit) & 1) != word[nph]:
            return res
        for a in (0, 1):
            for b in (0, 1):
                res.append((base | a | (b << (n - 1)), nph))
        return res
    verts = [(row, ph) for ph in range(p) for row in range(1 << n) if ((row >> cbit) & 1) == word[ph]]
    return verts, succ, n, cbit

def tarjan_scc(verts, succ):
    index = {}; low = {}; onstack = set(); stack = []; sccs = []; idx = 0
    for v0 in verts:
        if v0 in index: continue
        work = [(v0, iter(succ(*v0)))]
        index[v0] = low[v0] = idx; idx += 1; stack.append(v0); onstack.add(v0)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = idx; idx += 1; stack.append(w); onstack.add(w)
                    work.append((w, iter(succ(*w)))); advanced = True; break
                elif w in onstack:
                    low[v] = min(low[v], index[w])
            if advanced: continue
            work.pop()
            if work:
                u = work[-1][0]; low[u] = min(low[u], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop(); onstack.discard(w); comp.append(w)
                    if w == v: break
                sccs.append(comp)
    return sccs

def two_sided_check(word, r, col):
    # col: offset of the column to test (-1 or +1)
    verts, succ, n, cbit = two_sided_graph(word, r)
    sccs = tarjan_scc(verts, succ)
    cyc = []
    for comp in sccs:
        cs = set(comp)
        if len(comp) > 1 or any(w in cs for w in succ(*comp[0])):
            cyc.append(cs)
    ok_all = True; info = []
    for cs in cyc:
        # BFS classes modulo component period
        start = next(iter(cs)); level = {start: 0}; frontier = [start]
        while frontier:
            nf = []
            for v in frontier:
                for w in succ(*v):
                    if w in cs and w not in level:
                        level[w] = level[v] + 1; nf.append(w)
            frontier = nf
        g = 0
        for v in cs:
            for w in succ(*v):
                if w in cs:
                    g = __import__('math').gcd(g, level[v] + 1 - level[w])
        P = abs(g)
        cls = {}
        good = True
        for v in cs:
            k = level[v] % P
            val = (v[0] >> (cbit + col)) & 1
            if cls.setdefault(k, val) != val:
                good = False
        info.append((len(cs), P, good))
        ok_all = ok_all and good
    return ok_all, info

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'white':      # words 1 0^q, one-sided width K
        K = int(sys.argv[2])
        for q in range(int(sys.argv[3]), int(sys.argv[4]) + 1):
            w = [1] + [0] * q
            ok, col1, sz = one_sided_determined(w, K)
            print(f"1 0^{q}: K={K} determined={ok} |S|={sz} col+1={col1}")
    elif mode == 'black1':   # words 0 1^q, one-sided width K
        K = int(sys.argv[2])
        for q in range(int(sys.argv[3]), int(sys.argv[4]) + 1):
            w = [0] + [1] * q
            ok, col1, sz = one_sided_determined(w, K)
            print(f"0 1^{q}: K={K} determined={ok} |S|={sz} col+1={col1}")
    elif mode == 'black2':   # words 0 1^q, two-sided radius r, column -1
        r = int(sys.argv[2])
        for q in range(int(sys.argv[3]), int(sys.argv[4]) + 1):
            w = [0] + [1] * q
            ok, info = two_sided_check(w, r, -1)
            print(f"0 1^{q}: r={r} col-1 forced on all cyclic SCCs={ok} comps(size,period,ok)={info}")
    elif mode == 'word':     # arbitrary words, one-sided width K
        K = int(sys.argv[2])
        for s in sys.argv[3:]:
            w = [int(ch) for ch in s]
            ok, col1, sz = one_sided_determined(w, K)
            print(f"{s}: K={K} determined={ok} |S|={sz} col+1={col1}")
