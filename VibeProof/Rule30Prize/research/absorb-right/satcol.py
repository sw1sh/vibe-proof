# For the w-driven right half (start phase 0, ALL initial configs), decide which values x(n,1) can take.
# Encodes the light cone of cell (n,1) as CNF and calls cadical.
import sys, subprocess, os, tempfile
CADICAL = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/cadical')

def build(w, n, col=1, phase=0):
    P = len(w); wb = [int(ch) for ch in w]
    var = {}; clauses = []
    def v(t, p):
        if p == 0: return ('const', wb[(phase + t) % P])
        key = (t, p)
        if key not in var: var[key] = len(var) + 1
        return var[key]
    nv = [0]
    def lit(x, positive=True):
        return x
    # cells in cone of (n, col): (t, p) with 1 <= p <= col + n - t
    aux_base = [None]
    extra = []
    def newvar():
        k = ('aux', len(var)); var[k] = len(var) + 1; return var[k]
    def add(cl): clauses.append(cl)
    def eq_rule(z, a, b, c):
        # z = a xor (b or c); a may be const
        o = newvar()
        # o = b or c
        add([-b, o]); add([-c, o]); add([b, c, -o])
        if isinstance(a, tuple):
            if a[1] == 0: add([-z, o]); add([z, -o])
            else: add([z, o]); add([-z, -o])
        else:
            add([-z, a, o]); add([-z, -a, -o]); add([z, -a, o]); add([z, a, -o])
    for t in range(n):
        for p in range(1, col + n - t):  # (t+1, p) needs p <= col + n - (t+1)
            z = v(t + 1, p); a = v(t, p - 1); b = v(t, p); c = v(t, p + 1)
            eq_rule(z, a, b, c)
    target = v(n, col)
    return var, clauses, target

def solve(clauses, nvars, assumptions):
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
        f.write(f"p cnf {nvars} {len(clauses) + len(assumptions)}\n")
        for cl in clauses: f.write(' '.join(map(str, cl)) + ' 0\n')
        for a in assumptions: f.write(f"{a} 0\n")
        fn = f.name
    r = subprocess.run([CADICAL, '-q', fn], capture_output=True, text=True)
    os.unlink(fn)
    return r.returncode  # 10 SAT, 20 UNSAT

def possible_values(w, n, col=1, phase=0):
    var, clauses, target = build(w, n, col, phase)
    res = []
    for val in (0, 1):
        rc = solve(clauses, len(var), [target if val else -target])
        if rc == 10: res.append(val)
        elif rc != 20: raise Exception("solver error %d" % rc)
    return res

if __name__ == '__main__':
    w = sys.argv[1]; n0 = int(sys.argv[2]); n1 = int(sys.argv[3])
    for n in range(n0, n1):
        print(n, n % len(w), possible_values(w, n), flush=True)
