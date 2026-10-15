# Independent recomputation (verifier) of the period-2 bad class of the right strip, w = 01.
# Written from the Lean definitions (Rule30StripCertificates.lin3 / Cert.edgeOKb / checkGb), not from
# the worker's scripts.
#  node (phi, s): phi in {0,1}, s = (s[0..b-1]) columns 1..b; column 0 = wAt(phi), wAt(0)=0 (white), wAt(1)=1.
#  edge: (phi, s) -> ((phi+1)%2, lin3(wAt(phi) :: s ++ [x])) for x in {0,1}
#  rank classes outside `bad` carry a counter that advances at white phases; col1 at white = u(counter).
#  minimal closed bad class = forward closure of the non-labelable SCCs.
import sys, itertools
from math import gcd

def lin3(l):
    return tuple(l[i] ^ (l[i+1] | l[i+2]) for i in range(len(l) - 2))

def succs(b, node):
    phi, s = node
    c0 = 0 if phi == 0 else 1
    return [((phi + 1) % 2, lin3((c0,) + s + (x,))) for x in (0, 1)]

def graph(b):
    nodes = [(phi, s) for phi in (0, 1) for s in itertools.product((0, 1), repeat=b)]
    return nodes, {v: succs(b, v) for v in nodes}

def sccs(nodes, E):
    # iterative Tarjan
    index, low, onst, st, out, idx = {}, {}, set(), [], [], [0]
    for root in nodes:
        if root in index: continue
        stack = [(root, 0)]
        index[root] = low[root] = idx[0]; idx[0] += 1; st.append(root); onst.add(root)
        while stack:
            v, i = stack[-1]
            if i < len(E[v]):
                stack[-1] = (v, i + 1)
                w = E[v][i]
                if w not in index:
                    index[w] = low[w] = idx[0]; idx[0] += 1; st.append(w); onst.add(w)
                    stack.append((w, 0))
                elif w in onst:
                    low[v] = min(low[v], index[w])
            else:
                stack.pop()
                if stack:
                    low[stack[-1][0]] = min(low[stack[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = st.pop(); onst.discard(w); comp.append(w)
                        if w == v: break
                    out.append(comp)
    return out

def labelable(comp, E):
    cs = set(comp)
    internal = [(v, w) for v in comp for w in E[v] if w in cs]
    if not internal:
        return True
    # potentials: weight 1 on edges leaving a white (phi = 0) node
    pot = {comp[0]: 0}
    order = [comp[0]]
    for v in order:
        for w in E[v]:
            if w in cs and w not in pot:
                pot[w] = pot[v] + (1 if v[0] == 0 else 0)
                order.append(w)
    g = 0
    for v, w in internal:
        g = gcd(g, abs(pot[v] + (1 if v[0] == 0 else 0) - pot[w]))
    assert g > 0
    lab = {}
    for v in comp:
        if v[0] == 0:
            k = pot[v] % g
            c1 = v[1][0]
            if lab.setdefault(k, c1) != c1:
                return False
    return True

def bad_class(b):
    nodes, E = graph(b)
    comps = sccs(nodes, E)
    nonlab = [v for c in comps if not labelable(c, E) for v in c]
    B = set(nonlab)
    stack = list(nonlab)
    while stack:
        v = stack.pop()
        for w in E[v]:
            if w not in B:
                B.add(w); stack.append(w)
    return nodes, E, comps, B

def occurs(b, E, B, pat):
    # some path inside B, read at consecutive white (phase 0) nodes, spells pat in column 1
    S = {v for v in B if v[0] == 0 and v[1][0] == pat[0]}
    for y in pat[1:]:
        S2 = set()
        for v in S:
            for v1 in E[v]:
                if v1 in B:
                    for v2 in E[v1]:
                        if v2 in B and v2[1][0] == y:
                            S2.add(v2)
        S = S2
        if not S: return False
    return bool(S)

def gapword(gs):
    w = [1]
    for g in gs:
        w += [0] * g + [1]
    return w

if __name__ == '__main__':
    for b in range(3, 8):
        nodes, E, comps, B = bad_class(b)
        nb = len(nodes) - len(B)
        f11 = not occurs(b, E, B, [1, 1])
        f0 = [k for k in range(1, 9) if not occurs(b, E, B, [0] * k)]
        gaps = [g for g in range(0, 9) if occurs(b, E, B, gapword([g]))]
        pairs = [(g1, g2) for g1 in gaps for g2 in gaps if not occurs(b, E, B, gapword([g1, g2]))]
        bad_pairs = set(pairs)
        triples = [(g1, g2, g3) for g1 in gaps for g2 in gaps for g3 in gaps
                   if (g1, g2) not in bad_pairs and (g2, g3) not in bad_pairs
                   and not occurs(b, E, B, gapword([g1, g2, g3]))]
        print(f"b={b}: nodes={len(nodes)} bad={len(B)} ranks(if 1 per non-bad node)={nb + 1} "
              f"forbid11={f11} min_forbidden_zero_run={min(f0) if f0 else None} gap_alphabet={gaps} "
              f"forbidden_pairs={pairs} forbidden_triples(not containing a forbidden pair)={triples}")
    # compare with the packed certificates K5, K6 (rank 0 = bad)
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    for b, fn in ((5, 'K5_rankP.txt'), (6, 'K6_rankP.txt')):
        rankP = int(open(os.path.join(here, fn)).read().strip())
        nodes, E, comps, B = bad_class(b)
        def enc(s):
            return sum(bit << i for i, bit in enumerate(s))
        rk = {v: (rankP >> (16 * (v[0] * 2 ** b + enc(v[1])))) % 65536 for v in nodes}
        cert_bad = {v for v in nodes if rk[v] == 0}
        print(f"cert b={b}: rank-0 nodes={len(cert_bad)} distinct ranks={len(set(rk.values()))} "
              f"max rank={max(rk.values())} same set as my bad class: {cert_bad == B}")
        # rank monotone along edges?
        viol = sum(1 for v in nodes for w in E[v] if rk[w] > rk[v])
        print(f"   rank increases along an edge: {viol} edges")
