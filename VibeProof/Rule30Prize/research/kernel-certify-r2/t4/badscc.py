# Recompute bad SCCs for w (as in progB-avoid/lean/skel_export.py) and the gap-word language of the
# bad class at the white phase; independent reimplementation.
import sys, itertools
from collections import deque, defaultdict
def analyze(w, b, L=30, K=2):
    P = len(w)
    def succs(phi, s):
        c = int(w[phi]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
        base = 0
        for p in range(1, b): base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
        nphi = (phi + 1) % P
        return sorted(set((nphi, base | ((bit(b - 1) ^ (bit(b) | x)) << (b - 1))) for x in (0, 1)))
    nodes = [(phi, s) for phi in range(P) for s in range(1 << b)]
    adj = {v: succs(*v) for v in nodes}
    # Tarjan-free: Kosaraju
    order = []; seen = set()
    for v in nodes:
        if v in seen: continue
        stack = [(v, iter(adj[v]))]; seen.add(v)
        while stack:
            x, it = stack[-1]; nx = next(it, None)
            if nx is None: order.append(x); stack.pop()
            elif nx not in seen: seen.add(nx); stack.append((nx, iter(adj[nx])))
    radj = defaultdict(list)
    for v in nodes:
        for y in adj[v]: radj[y].append(v)
    comp = {}; nc = 0
    for v in reversed(order):
        if v in comp: continue
        st = [v]; comp[v] = nc
        while st:
            x = st.pop()
            for y in radj[x]:
                if y not in comp: comp[y] = nc; st.append(y)
        nc += 1
    members = defaultdict(list)
    for v in nodes: members[comp[v]].append(v)
    bads = []
    for c, mem in members.items():
        ms = set(mem)
        if not (len(mem) > 1 or mem[0] in adj[mem[0]]): continue
        # consistent labelling test: column 1 at white phases is a periodic counter along all cycles
        stn = mem[0]; par = {stn: None}; dq = deque([stn]); back = None
        while dq and back is None:
            x = dq.popleft()
            for y in adj[x]:
                if y not in ms: continue
                if y == stn: back = x; break
                if y not in par: par[y] = x; dq.append(y)
        path = []; x = back
        while x is not None: path.append(x); x = par[x]
        path.reverse()
        wd = [x[1] & 1 for x in path if w[x[0]] == '0']; Lw = len(wd)
        m = next(d for d in range(1, Lw + 1) if Lw % d == 0 and all(wd[i] == wd[i - d] for i in range(d, Lw)))
        wd = wd[:m]; lab = {stn: 0}; dq = deque([stn]); ok = True
        while dq and ok:
            x = dq.popleft()
            if w[x[0]] == '0':
                if (x[1] & 1) != wd[lab[x] % m]: ok = False; break
                np_ = (lab[x] + 1) % m
            else: np_ = lab[x]
            for y in adj[x]:
                if y not in ms: continue
                if y in lab:
                    if lab[y] != np_: ok = False; break
                else: lab[y] = np_; dq.append(y)
        if not ok: bads.append(c)
    res = {'b': b, 'nbad': len(bads)}
    if len(bads) != 1: return res
    B = set(members[bads[0]]); res['size'] = len(B)
    fph = w.index('0')
    S = {v: [u for u in adj[v] if u in B] for v in B}
    fp = [v for v in B if v[0] == fph]
    nxt = {}
    for v in fp:
        cur = {v}
        for _ in range(P): cur = set(u for x in cur for u in S[x])
        nxt[v] = cur
    words = {}
    for v in fp: words.setdefault(str(v[1] & 1), set()).add(v)
    for _ in range(L - 1):
        nw = {}
        for wd, ns in words.items():
            sc = set(u for i in ns for u in nxt[i])
            for y in (0, 1):
                sel = set(i for i in sc if (i[1] & 1) == y)
                if sel: nw[wd + str(y)] = sel
        words = nw
    allowed = defaultdict(set)
    for x in words:
        ones = [i for i, ch in enumerate(x) if ch == '1']
        gaps = [c - a - 1 for a, c in zip(ones, ones[1:])]
        for k in range(1, K + 1):
            for i in range(len(gaps) - k + 1): allowed[k].add(tuple(gaps[i:i + k]))
    alph = sorted(set(g for (g,) in allowed[1]))
    res['alph'] = alph
    res['forb2'] = [''.join(map(str, t)) for t in itertools.product(alph, repeat=2) if t not in allowed[2]]
    mf = {}
    for k in range(1, K + 1):
        mf[k] = [''.join(map(str, t)) for t in itertools.product(alph, repeat=k) if t not in allowed[k] and (k == 1 or (t[1:] in allowed[k - 1] and t[:-1] in allowed[k - 1]))]
    res['minforb'] = mf
    return res
w = sys.argv[1]
for b in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
    print(analyze(w, b), flush=True)
