# My own CNF encoding (independent of satper.py) of: right half of rule 30 driven at column 0 by w^inf
# (phase 0), arbitrary initial configuration.  Query: can x(n,1) != x(n+Q,1)?  (UNSAT = forced equal.)
import sys, subprocess, os
def encode(w, n, Q):
    N = n + Q; P = len(w); d = [int(ch) for ch in w]
    var = {}
    def X(t, p):
        assert 1 <= p <= 1 + N - t, (t, p)
        if (t, p) not in var: var[(t, p)] = len(var) + 1
        return var[(t, p)]
    for t in range(N + 1):
        for p in range(1, 2 + N - t): X(t, p)
    nv = [len(var)]
    def fresh():
        nv[0] += 1; return nv[0]
    cls = []
    for t in range(1, N + 1):
        for p in range(1, 2 + N - t):
            z = X(t, p); b = X(t - 1, p); c = X(t - 1, p + 1)
            o = fresh()  # o <-> b or c
            cls += [[-b, o], [-c, o], [-o, b, c]]
            if p == 1:
                if d[(t - 1) % P] == 0: cls += [[-z, o], [z, -o]]       # z = o
                else: cls += [[z, o], [-z, -o]]                         # z = not o
            else:
                a = X(t - 1, p - 1)                                     # z = a xor o
                cls += [[-z, a, o], [-z, -a, -o], [z, -a, o], [z, a, -o]]
    u = X(n, 1); v = X(N, 1)
    cls += [[u, v], [-u, -v]]
    return nv[0], cls
def write(fn, nv, cls):
    with open(fn, 'w') as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
if __name__ == '__main__':
    w = sys.argv[1]; Q = int(sys.argv[2]); n0 = int(sys.argv[3]); n1 = int(sys.argv[4]); outdir = sys.argv[5]
    for n in range(n0, n1):
        nv, cls = encode(w, n, Q)
        write(os.path.join(outdir, f"q_{w}_{Q}_{n}.cnf"), nv, cls)
        print(n, nv, len(cls))
