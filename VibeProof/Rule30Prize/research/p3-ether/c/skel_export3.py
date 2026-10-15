# Export a "bad-class" strip certificate for word w at width b as Lean data (same packing as export_cert.py).
# Ranks: topological order of the SCC condensation (sources high, edges never increase rank).
# Good SCCs: consistent position labelling of the output (column 1 at white phases); trivial SCCs: m = 1.
# The unique bad SCC (inconsistent) gets rank `bad`; the script asserts there is exactly one.
# Also prints the skeleton (cells constant over the bad SCC, per phase).
import sys
from collections import deque
sys.set_int_max_str_digits(0)
w = sys.argv[1]; b = int(sys.argv[2]); name = sys.argv[3]; out = sys.argv[4]
P = len(w)
N = P << b
def succs(phi, s):
    c = int(w[phi]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
    base = 0
    for p in range(1, b):
        base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
    nphi = (phi + 1) % P
    res = []
    for x in (0, 1):
        nb = bit(b - 1) ^ (bit(b) | x)
        res.append((nphi, base | (nb << (b - 1))))
    return res  # successor for x = 0, x = 1 (may coincide)
nodes = [(phi, s) for phi in range(P) for s in range(1 << b)]
adj = {v: sorted(set(succs(*v))) for v in nodes}
# Kosaraju
order = []; seen = set()
for v in nodes:
    if v in seen: continue
    stack = [(v, iter(adj[v]))]; seen.add(v)
    while stack:
        x, it = stack[-1]
        nx = next(it, None)
        if nx is None: order.append(x); stack.pop()
        elif nx not in seen: seen.add(nx); stack.append((nx, iter(adj[nx])))
radj = {v: [] for v in nodes}
for v in nodes:
    for y in adj[v]: radj[y].append(v)
comp = {}; nc = 0
for v in reversed(order):
    if v in comp: continue
    stack = [v]; comp[v] = nc
    while stack:
        x = stack.pop()
        for y in radj[x]:
            if y not in comp: comp[y] = nc; stack.append(y)
    nc += 1
rank = {v: nc - 1 - comp[v] for v in nodes}
members = {}
for v in nodes: members.setdefault(rank[v], []).append(v)
pos = {}; per = [1] * nc; words = [[0] for _ in range(nc)]; bad = []
for r, mem in members.items():
    ms = set(mem)
    nontriv = len(mem) > 1 or any(y == mem[0] for y in adj[mem[0]])
    if not nontriv:
        for v in mem: pos[v] = 0
        continue
    st = mem[0]
    # cycle through st
    par = {st: None}; dq = deque([st]); back = None
    while dq and back is None:
        x = dq.popleft()
        for y in adj[x]:
            if y not in ms: continue
            if y == st: back = x; break
            if y not in par: par[y] = x; dq.append(y)
    path = []; x = back
    while x is not None: path.append(x); x = par[x]
    path.reverse()
    wd = [x[1] & 1 for x in path if w[x[0]] == '0']
    L = len(wd)
    m = next(d for d in range(1, L + 1) if L % d == 0 and all(wd[i] == wd[i - d] for i in range(d, L)))
    wd = wd[:m]
    lab = {st: 0}; dq = deque([st]); ok = True
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
    if ok:
        for v in mem: pos[v] = lab[v]
        per[r] = m; words[r] = wd
    else:
        bad.append(r)
        for v in mem: pos[v] = 0
# merge the bad SCCs into one class: the convex hull of the bad ranks in the condensation DAG
# (every SCC on a path between two bad SCCs); ranks are re-assigned so the merged class is one rank.
nbad_sccs = len(bad)
if len(bad) > 1:
    # condensation graph on ranks
    cadj = {r: set() for r in range(nc)}
    for v in nodes:
        for y in adj[v]:
            if rank[y] != rank[v]: cadj[rank[v]].add(rank[y])
    radj2 = {r: set() for r in range(nc)}
    for r in cadj:
        for q in cadj[r]: radj2[q].add(r)
    def reach(srcs, g):
        seen = set(srcs); st = list(srcs)
        while st:
            x = st.pop()
            for y in g[x]:
                if y not in seen: seen.add(y); st.append(y)
        return seen
    down = reach(bad, cadj); up = reach(bad, radj2)
    hull = down & up
    # new ranks: collapse hull into one class; keep a topological order (ranks non-increasing along edges)
    # condensation nodes: hull merged as 'H'
    def cls(r): return 'H' if r in hull else r
    cnodes = set(cls(r) for r in range(nc))
    cedges = {c: set() for c in cnodes}
    for r in cadj:
        for q in cadj[r]:
            a, b2 = cls(r), cls(q)
            if a != b2: cedges[a].add(b2)
    # topological order (Kahn), sources first -> highest rank
    indeg = {c: 0 for c in cnodes}
    for c in cedges:
        for d in cedges[c]: indeg[d] += 1
    order2 = []; q0 = [c for c in cnodes if indeg[c] == 0]
    while q0:
        c = q0.pop(); order2.append(c)
        for d in cedges[c]:
            indeg[d] -= 1
            if indeg[d] == 0: q0.append(d)
    assert len(order2) == len(cnodes), "merged condensation not acyclic"
    newrank = {c: len(order2) - 1 - i for i, c in enumerate(order2)}
    oldper, oldwords = per, words
    rank = {v: newrank[cls(rank[v])] for v in nodes}
    nc = len(order2)
    per = [1] * nc; words = [[0] for _ in range(nc)]
    for c in cnodes:
        if c != 'H': per[newrank[c]] = oldper[c]; words[newrank[c]] = oldwords[c]
    bad = [newrank['H']]
    members = {}
    for v in nodes: members.setdefault(rank[v], []).append(v)
    for v in members[bad[0]]: pos[v] = 0
assert len(bad) == 1, bad
bad = bad[0]
B = members[bad]
print(f"  ({nbad_sccs} bad SCCs merged into one class of {len(B)} nodes)")
print(f"w={w} b={b}: {nc} SCC ranks, bad rank {bad} with {len(B)} nodes; good nontrivial words",
      sorted(set(''.join(map(str, words[r])) for r in range(nc) if per[r] > 1 or words[r] != [0])))
# independent check of the edge conditions
nextpos = lambda r, p, phi: p if w[phi] == '1' else (p + 1) % per[r]
for v in nodes:
    for y in adj[v]:
        assert rank[y] <= rank[v]
        if rank[y] == rank[v] and rank[v] != bad:
            assert pos[y] == nextpos(rank[v], pos[v], v[0])
            if w[v[0]] == '0': assert (v[1] & 1) == words[rank[v]][pos[v]]
# skeleton
skel = {}
for phi in range(P):
    S = [s for (q, s) in B if q == phi]
    row = ''
    for p in range(1, b + 1):
        vals = set((s >> (p - 1)) & 1 for s in S)
        row += str(vals.pop()) if len(vals) == 1 else '*'
    skel[phi] = row
    print(f"  skeleton phase {phi} ({w[phi]}): {row}  ({len(S)} nodes)")
assert max(rank.values()) < 65536 and max(pos.values()) < 256 and max(per) < 256 and max(len(u) for u in words) <= 64
idx = lambda phi, s: phi * (1 << b) + s
rankP = sum(rank[v] << (16 * idx(*v)) for v in nodes)
posP = sum(pos[v] << (8 * idx(*v)) for v in nodes)
perP = sum(m << (8 * r) for r, m in enumerate(per))
wordP = sum((1 << (64 * r + j)) for r in range(nc) for j, x in enumerate(words[r]) if x)
def bl(xs): return '[' + ', '.join('true' if x else 'false' for x in xs) + ']'
with open(out, 'w') as f:
    f.write(f"-- bad-class certificate for w = {w}, strip width b = {b}; generated by skel_export.py\n")
    f.write(f"def {name}_w : List Bool := {bl([c == '1' for c in w])}\n")
    f.write(f"def {name}_b : Nat := {b}\n")
    f.write(f"def {name}_nranks : Nat := {nc}\n")
    f.write(f"def {name}_bad : Nat := {bad}\n")
    f.write(f"def {name}_rankP : Nat := {rankP}\n")
    f.write(f"def {name}_posP : Nat := {posP}\n")
    f.write(f"def {name}_perP : Nat := {perP}\n")
    f.write(f"def {name}_wordP : Nat := {wordP}\n")
print("written", out)
