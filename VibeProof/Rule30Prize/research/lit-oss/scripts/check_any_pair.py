import sys, math
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/lit-oss/scripts')
from verify_word_exclusions import two_sided_graph, tarjan_scc
def any_pair_check(word, r):
    verts, succ, n, cbit = two_sided_graph(word, r)
    sccs = tarjan_scc(verts, succ)
    results = []
    for comp in sccs:
        cs = set(comp)
        if not (len(comp) > 1 or any(w in cs for w in succ(*comp[0]))):
            continue
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
                    g = math.gcd(g, level[v] + 1 - level[w])
        P = abs(g)
        const_cols = []
        for col in range(-r, r + 1):
            cls = {}; good = True
            for v in cs:
                k = level[v] % P; val = (v[0] >> (cbit + col)) & 1
                if cls.setdefault(k, val) != val:
                    good = False; break
            if good: const_cols.append(col)
        pair = any((c in const_cols and c + 1 in const_cols) for c in range(-r, r))
        results.append((len(cs), P, const_cols, pair))
    return all(x[3] for x in results), results
r = int(sys.argv[1])
for s in sys.argv[2:]:
    ok, res = any_pair_check([int(ch) for ch in s], r)
    print(f"{s}: r={r} every cyclic SCC has an adjacent forced pair: {ok}; comps={[(a,b,c,d) for a,b,c,d in res]}")
