"""Exact (SAT) check: for driver word w = 1^s 0^r u (t1 = 0) and ALL initial right-half rows,
is column 1 on the window [s, s+P) a constant (row-independent) sequence?

Independent CNF encoder; solver = cadical from the Lean toolchain.
UNSAT  => every time in the window has a row-independent value (the strong form of the proof).
SAT    => a concrete initial row gives a different window (we decode and re-simulate it).
"""
import os, subprocess, sys, random, itertools, tempfile

CADICAL = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/cadical')

def simulate(word, row0, tmax):
    """row0: list of bits for columns 1..len(row0); returns col1[t] for t = 0..tmax."""
    P = len(word)
    row = list(row0)
    out = [row[0]]
    for t in range(tmax):
        d = word[t % P]
        new = []
        for i in range(len(row) - 1):
            l = d if i == 0 else row[i - 1]
            new.append(l ^ (row[i] | row[i + 1]))
        row = new
        out.append(row[0])
    return out

def encode(word, tmax):
    P = len(word)
    var = {}
    def v(t, p):
        if (t, p) not in var:
            var[(t, p)] = len(var) + 1
        return var[(t, p)]
    # allocate cells in the cone of (tmax, 1): p in 1..1+tmax-t
    for t in range(tmax + 1):
        for p in range(1, 2 + tmax - t):
            v(t, p)
    nv = [len(var)]
    def fresh():
        nv[0] += 1
        return nv[0]
    cl = []
    for t in range(1, tmax + 1):
        for p in range(1, 2 + tmax - t):
            z = v(t, p)
            b = v(t - 1, p)
            c = v(t - 1, p + 1)
            o = fresh()
            cl += [[-b, o], [-c, o], [b, c, -o]]
            if p == 1:
                a = word[(t - 1) % P]
                if a == 0:
                    cl += [[-z, o], [z, -o]]
                else:
                    cl += [[z, o], [-z, -o]]
            else:
                a = v(t - 1, p - 1)
                cl += [[-z, a, o], [-z, -a, -o], [z, -a, o], [z, a, -o]]
    return var, nv[0], cl

def solve(nvars, clauses):
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')
        name = f.name
    try:
        res = subprocess.run([CADICAL, '-q', name], capture_output=True, text=True, timeout=50)
    finally:
        os.unlink(name)
    lines = res.stdout.splitlines()
    status = None
    model = {}
    for ln in lines:
        if ln.startswith('s '):
            status = ln[2:].strip()
        elif ln.startswith('v '):
            for x in ln[2:].split():
                x = int(x)
                if x != 0:
                    model[abs(x)] = x > 0
    return status, model

def check(word, s, rng):
    P = len(word)
    tmax = s + P - 1
    pred = simulate(word, [rng.getrandbits(1) for _ in range(tmax + 1)], tmax)
    var, nvars, cl = encode(word, tmax)
    diff = []
    for t in range(s, s + P):
        x = var[(t, 1)]
        diff.append(x if pred[t] == 0 else -x)
    cl.append(diff)
    status, model = solve(nvars, cl)
    if status == 'SATISFIABLE':
        row0 = [int(model.get(var[(0, p)], False)) for p in range(1, tmax + 2)]
        alt = simulate(word, row0, tmax)
        differs = [t for t in range(s, s + P) if alt[t] != pred[t]]
        return 'SAT', differs
    return status, None

def rmin(k):
    return 1 + 9 * ((k + 9) // 2)

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]))
    mode = sys.argv[2]
    if mode == 'control':
        # encoding sanity: these should be SAT (window depends on the row)
        for wstr in ('1' * 8 + '0' * 36, '1' * 8 + '0' * 45 + '01', '1' * 5 + '0' * 37, '1' * 9 + '0' * 5):
            word = [int(ch) for ch in wstr]
            s = wstr.index('0')
            print('control', wstr, check(word, s, rng))
    else:
        s_list = [int(x) for x in sys.argv[3].split(',')]
        k_list = [int(x) for x in sys.argv[4].split(',')]
        delta = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        maxu = int(sys.argv[6]) if len(sys.argv) > 6 else 8
        for s in s_list:
            for k in k_list:
                us = [list(u) for u in itertools.product([0, 1], repeat=k)]
                if len(us) > maxu:
                    us = rng.sample(us, maxu)
                r = rmin(k) + delta
                res = []
                for u in us:
                    word = [1] * s + [0] * r + u
                    st, info = check(word, s, rng)
                    res.append((''.join(map(str, u)), st, info))
                nunsat = sum(1 for x in res if x[1] == 'UNSATISFIABLE')
                print(f"s={s} k={k} r={r} (rmin={rmin(k)}): UNSAT {nunsat}/{len(res)}",
                      [x for x in res if x[1] != 'UNSATISFIABLE'])
                sys.stdout.flush()
