# Convert B-edge-trap certificates (choice semantics) to column-(b+1) inputs (catalog lin3 semantics),
# check them independently, and emit Lean certificate theorems.
import sys, os
B = 20
E = ['0011', '0110', '1101', '0101', '0011', '0001', '0001']
ALIGN = {'0001': [(5, 0), (6, 0)], '0011': [(0, 0), (1, 3), (4, 0)], '0111': [(2, 2)]}
SRC = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/B-edge-trap'
def ether(j, ph): return E[j % 7][ph % 4] == '1'
def lin3(l): return [l[i] ^ (l[i + 1] | l[i + 2]) for i in range(len(l) - 2)]
def step(w, st, x):
    ph, s = st
    return ((ph + 1) % 4, tuple(lin3([w[ph % 4] == '1'] + list(s) + [x])))
def white(w, st): return w[st[0] % 4] == '0'
def col1(st): return st[1][0] if st[1] else False
def run(w, st, xs):
    for x in xs: st = step(w, st, x)
    return st
def to_x(w, st, choices):
    xs = []
    for ch in choices:
        s = st[1]; c = (ch == '1')
        x = False if s[B - 1] else (c ^ s[B - 2])   # col b = s[B-1], col b-1 = s[B-2]
        xs.append(x); st2 = step(w, st, x)
        assert st2[1][B - 1] == ((not s[B - 2]) if s[B - 1] else c)
        st = st2
    return xs, st
out = {}
for w in ['0001', '0011', '0111']:
    certs = []
    for line in open(os.path.join(SRC, f'cert_{w}_20.txt')):
        p = line.split()
        ph, sv = int(p[1]), int(p[2])
        s = tuple(bool((sv >> i) & 1) for i in range(B))
        # identify the alignment
        hits = [(j0, sh) for (j0, sh) in ALIGN[w] if s == tuple(ether(j0 + i + 1, (ph + sh) % 4) for i in range(B))]
        assert len(hits) == 1, (w, ph, hits)
        j0, sh = hits[0]
        path = '' if p[4] == '-' else p[4]; c1 = p[6]; c2 = p[7]
        x0 = (ph, s)
        P, y = to_x(w, x0, path)
        A, yA = to_x(w, y, c1 + c2); Bx, yB = to_x(w, y, c2 + c1)
        assert yA == y and yB == y and len(A) == len(Bx) and len(A) % 4 == 0
        # first white offset where col1 differs
        sa, sb = y, y; j0w = None
        for j in range(len(A)):
            if white(w, sa) and col1(sa) != col1(sb): j0w = j; break
            sa = step(w, sa, A[j]); sb = step(w, sb, Bx[j])
        assert j0w is not None
        certs.append((ph, j0, sh, P, A, Bx, j0w))
    out[w] = certs
    print(w, len(certs), 'certs; max lens', max(len(c[3]) for c in certs), max(len(c[4]) for c in certs))
def bl(xs): return '[' + ', '.join('true' if x else 'false' for x in xs) + ']'
groups = []
for w in ['0001', '0011', '0111']:
    cs = out[w]
    for k in range(0, len(cs), 4): groups.append((w, cs[k:k + 4]))
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'src', 'KC')
names = []
for gi, (w, cs) in enumerate(groups):
    nm = f'EtherTrapCerts{gi}'; names.append(nm)
    with open(os.path.join(base, nm + '.lean'), 'w') as f:
        f.write('import KC.EtherTrap\n\n/-! Kernel-checked certificates for `' + w + '` (data: `B-edge-trap/cert_' + w + '_20.txt`, converted to\ncolumn-`21` inputs): from each pure-ether node of width `20`, a path to a node with two closed walks of\nequal length whose white-phase outputs differ. -/\n\n')
        f.write('namespace KC.EtherTrap\nopen Ruliology.CellularAutomata Rule30Ether\n\n')
        for (ph, j0, sh, P, A, Bx, j0w) in cs:
            f.write(f'theorem cert_{w}_{j0}_{ph} : certOK w{w} ({ph}, etherRow {j0} (({ph} + {sh}) % 4) 20)\n    {bl(P)}\n    {bl(A)}\n    {bl(Bx)}\n    {j0w} = true := by decide +kernel\n\n')
        f.write('end KC.EtherTrap\n')
print('cert modules', names)
