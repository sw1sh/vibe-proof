# SAT test: for the w-driven right half (start phase 0, ALL initial configurations X),
# is x(n,1) == x(n+Q,1) forced?  If forced for all n in [N0, N0+|w|), then column 1 is periodic
# with period Q from time N0 on, for every X (and every start phase, after <= |w| extra steps).
import sys, subprocess, os, tempfile
CADICAL = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/cadical')

def cone_cnf(w, n_top, col=1, phase=0):
    """CNF for all cells in the backward light cone of (n_top, col) for the w-driven right half.
    Returns (nvars, clauses, cellvar) where cellvar(t,p) gives the var of cell (t,p) (p>=1) in the cone."""
    P = len(w); wb = [int(ch) for ch in w]
    idx = {}; clauses = []; cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    def v(t, p):
        if p == 0: return ('c', wb[(phase + t) % P])
        k = (t, p)
        if k not in idx: idx[k] = new()
        return idx[k]
    for t in range(n_top):
        for p in range(1, col + n_top - t):
            z = v(t + 1, p); a = v(t, p - 1); b = v(t, p); c = v(t, p + 1)
            o = new()
            clauses += [[-b, o], [-c, o], [b, c, -o]]
            if isinstance(a, tuple):
                if a[1] == 0: clauses += [[-z, o], [z, -o]]
                else: clauses += [[z, o], [-z, -o]]
            else:
                clauses += [[-z, a, o], [-z, -a, -o], [z, -a, o], [z, a, -o]]
    return cnt, clauses, v

def run_cadical(nv, clauses, extra, proof=None):
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
        f.write(f"p cnf {nv} {len(clauses) + len(extra)}\n")
        for cl in clauses: f.write(' '.join(map(str, cl)) + ' 0\n')
        for cl in extra: f.write(' '.join(map(str, cl)) + ' 0\n')
        fn = f.name
    args = [CADICAL, '-q', fn] + ([proof] if proof else [])
    r = subprocess.run(args, capture_output=True, text=True)
    os.unlink(fn)
    if r.returncode not in (10, 20): raise Exception("cadical error %d %s" % (r.returncode, r.stderr[:200]))
    return r.returncode == 10

def forced_period(w, n, Q, phase=0):
    cnt, clauses, v = cone_cnf(w, n + Q, 1, phase)
    a = v(n, 1); b = v(n + Q, 1)
    sat = run_cadical(cnt[0], clauses, [[a, b], [-a, -b]])
    return not sat

def find_N0(w, Q, nmax=200, verbose=False):
    P = len(w); run = 0; n = 0
    while n <= nmax:
        if forced_period(w, n, Q):
            run += 1
            if run == P: return n - P + 1
        else:
            run = 0
        if verbose: print(n, run, flush=True)
        n += 1
    return None

if __name__ == '__main__':
    w = sys.argv[1]; Q = int(sys.argv[2]); nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    N0 = find_N0(w, Q, nmax)
    print(w, "Q =", Q, "N0 =", N0)
