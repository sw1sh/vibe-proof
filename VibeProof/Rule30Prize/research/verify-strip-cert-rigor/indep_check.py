# Independent re-implementation of Cert.check / Cert.checkG from StripCertCore.lean,
# reading the packed tables directly out of the Inst_*.lean files.
import re, sys
sys.set_int_max_str_digits(0)

def parse(path):
    txt = open(path).read()
    d = {}
    for key in ['w', 'b', 'nranks', 'rankP', 'posP', 'perP', 'wordP']:
        m = re.search(r'def \w+_' + key + r' : (?:List Bool|Nat) := (.+)\n', txt)
        d[key] = m.group(1).strip()
    w = [x.strip() == 'true' for x in d['w'].strip('[]').split(',')]
    return w, int(d['b']), int(d['nranks']), int(d['rankP']), int(d['posP']), int(d['perP']), int(d['wordP'])

def lin3(l):
    return [l[i] ^ (l[i+1] or l[i+2]) for i in range(len(l) - 2)]

def enc(s):
    return sum((1 << i) for i, x in enumerate(s) if x)

def all_lists(n):
    if n == 0: return [[]]
    prev = all_lists(n - 1)
    return [[False] + l for l in prev] + [[True] + l for l in prev]

def run(path):
    w, b, nranks, rankP, posP, perP, wordP = parse(path)
    P = len(w)
    wAt = lambda phi: w[phi] if phi < P else False
    idx = lambda phi, s: phi * 2**b + enc(s)
    rk = lambda phi, s: (rankP >> (16 * idx(phi, s))) % 65536
    ps = lambda phi, s: (posP >> (8 * idx(phi, s))) % 256
    m = lambda r: (perP >> (8 * r)) % 256
    u = lambda r, p: (wordP >> (64 * r + p)) % 2 == 1
    def nextPos(r, p, phi): return p if wAt(phi) else (p + 1) % m(r)
    def edgeOK(phi, s, s2):
        phi2 = (phi + 1) % P; r = rk(phi, s)
        if not rk(phi2, s2) <= r: return False
        if rk(phi2, s2) != r: return True
        return ps(phi2, s2) == nextPos(r, ps(phi, s), phi) and (wAt(phi) or ((s[0] if s else False) == u(r, ps(phi, s))))
    ok = True; nedges = 0; npres = 0
    for phi in range(P):
        for s in all_lists(b):
            for x in [False, True]:
                s2 = lin3([wAt(phi)] + s + [x])
                assert len(s2) == b
                nedges += 1
                if not edgeOK(phi, s, s2): ok = False
                if rk((phi + 1) % P, s2) == rk(phi, s): npres += 1
    okG = True
    for r in range(nranks):
        if not m(r) > 0: okG = False; continue
        for p in range(m(r)):
            for phi in range(P):
                q = (p, phi)
                for _ in range(m(r) * P):
                    q = (nextPos(r, q[0], q[1]), (q[1] + 1) % P)
                if q != (p, phi): okG = False
    for phi in range(P):
        for s in all_lists(b):
            if not (rk(phi, s) < nranks and ps(phi, s) < m(rk(phi, s))): okG = False
    # terminal structure: ranks that carry rank-preserving edges, with their (m, u) words
    pres = {}
    for phi in range(P):
        for s in all_lists(b):
            for x in [False, True]:
                s2 = lin3([wAt(phi)] + s + [x])
                r = rk(phi, s)
                if rk((phi + 1) % P, s2) == r:
                    pres.setdefault(r, 0); pres[r] += 1
    words = {r: ''.join('1' if u(r, p) else '0' for p in range(m(r))) for r in pres}
    print(path.split('/')[-1], 'w=' + ''.join('1' if x else '0' for x in w), 'b=%d' % b, 'P=%d' % P,
          'edges=%d' % nedges, 'rank-preserving=%d' % npres, 'check=%s' % ok, 'checkG=%s' % okG,
          'ranks with cycles=%d' % len(pres), 'distinct u words=%s' % sorted(set(words.values())))

for p in sys.argv[1:]:
    run(p)
