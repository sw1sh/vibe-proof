# "leftmost-1" abstraction test for absorption of the w-driven right half.
# Mode of a configuration X at phase 0: ell(X) = (index of first 1) - 1, classes 0..L and '>L' (= L+1).
# For each class we compute by SAT: possible column-1 output words over one period, and possible next classes.
# Sound over-approximation: real sequence (ell_k) is a path. If every nontrivial SCC has a single output
# word on all its nodes (and every node's output is unique), column 1 is eventually periodic for EVERY X.
import sys, subprocess, os, tempfile, itertools, time
sys.path.insert(0, '.')
from satper import cone_cnf, CADICAL

def solve(nv, clauses, extra):
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
        f.write(f"p cnf {nv} {len(clauses) + len(extra)}\n")
        for cl in clauses: f.write(' '.join(map(str, cl)) + ' 0\n')
        for cl in extra: f.write(' '.join(map(str, cl)) + ' 0\n')
        fn = f.name
    r = subprocess.run([CADICAL, '-q', fn], capture_output=True, text=True); os.unlink(fn)
    if r.returncode == 20: return None
    if r.returncode != 10: raise Exception("cadical error")
    vals = {}
    for line in r.stdout.splitlines():
        if line.startswith('v'):
            for tok in line.split()[1:]:
                k = int(tok)
                if k: vals[abs(k)] = k > 0
    return vals

def analyze(w, L, verbose=False):
    P = len(w)
    # cone: need column 1 at times 0..P-1 and config at time P on columns 1..L+1
    # top cell (P, L+1) cone covers (P, 1..L+1)? cone_cnf(n_top, col) covers cells (t,p) with p <= col + n_top - t.
    # Use n_top = P, col = L+1: covers all (t, p) with p <= L+1+P-t, includes column 1 at all t <= P.
    cnt, clauses, v = cone_cnf(w, P, L + 1, 0)
    nv = cnt[0]
    def cls_constraint(t, c):
        # constraint that config at time t has class c (cells (t, 1..))
        if c <= L: return [[-v(t, p)] for p in range(1, c + 1)] + [[v(t, c + 1)]]
        return [[-v(t, p)] for p in range(1, L + 2)]
    out_vars = [v(t, 1) for t in range(P)]
    nodes = {}
    for c in range(L + 2):
        base = cls_constraint(0, c)
        outs = set(); nexts = set()
        # enumerate output words
        blocking = []
        while True:
            sol = solve(nv, clauses, base + blocking)
            if sol is None: break
            o = tuple(int(sol.get(x, False)) for x in out_vars)
            outs.add(o)
            blocking.append([(-x if o[i] else x) for i, x in enumerate(out_vars)])
            if len(outs) > 8: break
        for c2 in range(L + 2):
            if solve(nv, clauses, base + cls_constraint(P, c2)) is not None:
                nexts.add(c2)
        nodes[c] = (outs, nexts)
        if verbose:
            print(f"class {c if c <= L else '>'+str(L)}: outputs {[''.join(map(str,o)) for o in outs]} next {sorted(nexts)}", flush=True)
    return nodes

def scc_test(nodes):
    # Tarjan on class graph
    idx = {}; low = {}; st = []; on = set(); comps = []; counter = [0]
    sys.setrecursionlimit(10000)
    def strong(u):
        idx[u] = low[u] = counter[0]; counter[0] += 1; st.append(u); on.add(u)
        for x in nodes[u][1]:
            if x not in idx: strong(x); low[u] = min(low[u], low[x])
            elif x in on: low[u] = min(low[u], idx[x])
        if low[u] == idx[u]:
            comp = []
            while True:
                x = st.pop(); on.discard(x); comp.append(x)
                if x == u: break
            comps.append(comp)
    for u in nodes:
        if u not in idx: strong(u)
    ok = True; report = []
    for comp in comps:
        nontriv = len(comp) > 1 or comp[0] in nodes[comp[0]][1]
        if not nontriv: continue
        outs = set()
        for u in comp: outs |= nodes[u][0]
        report.append((sorted(comp), [''.join(map(str, o)) for o in outs]))
        if len(outs) > 1: ok = False
    return ok, report

if __name__ == '__main__':
    w = sys.argv[1]; L = int(sys.argv[2]); verbose = len(sys.argv) > 3
    t0 = time.time()
    nodes = analyze(w, L, verbose)
    ok, report = scc_test(nodes)
    print(w, "L =", L, "PASS" if ok else "FAIL", "%.1fs" % (time.time() - t0))
    for comp, outs in report: print("  SCC", comp, "outputs", outs)
