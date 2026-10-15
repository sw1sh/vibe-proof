# Independent re-check of the packed Lean certificate tables (Inst_*.lean) in Python.
# Re-implements lin3, enc, idx, rk, ps, m, u, nextPos, edgeOK, check, checkG from the Lean source
# semantics, written from scratch (not importing cert.py), and checks them over all nodes/edges.
import sys, re
sys.set_int_max_str_digits(0)
LEAN = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/newideas/lean/'

def parse_inst(name):
    src = open(LEAN + 'Inst_' + name + '.lean').read()
    tail = src[src.index('-- certificate for'):]
    def nat(field):
        mm = re.search(r'def ' + re.escape(name) + '_' + field + r' : Nat := (\d+)', tail)
        return int(mm.group(1))
    wl = re.search(r'def ' + re.escape(name) + r'_w : List Bool := \[([^\]]*)\]', tail).group(1)
    w = [x.strip() == 'true' for x in wl.split(',')]
    return dict(w=w, b=nat('b'), nranks=nat('nranks'), rankP=nat('rankP'), posP=nat('posP'),
                perP=nat('perP'), wordP=nat('wordP'))

def lin3(l):
    return [l[i] ^ (l[i + 1] | l[i + 2]) for i in range(len(l) - 2)]

def enc(s):  # little endian
    v = 0
    for i, x in enumerate(s):
        if x: v |= 1 << i
    return v

def all_lists(n):
    for v in range(1 << n):
        yield [bool((v >> i) & 1) for i in range(n)]

class C:
    def __init__(self, d):
        self.__dict__.update(d)
        self.P = len(self.w)
    def wAt(self, phi): return self.w[phi] if phi < self.P else False
    def idx(self, phi, s): return phi * 2 ** self.b + enc(s)
    def rk(self, phi, s): return (self.rankP >> (16 * self.idx(phi, s))) % 65536
    def ps(self, phi, s): return (self.posP >> (8 * self.idx(phi, s))) % 256
    def m(self, r): return (self.perP >> (8 * r)) % 256
    def u(self, r, p): return (self.wordP >> (64 * r + p)) % 2 == 1
    def nextPos(self, r, p, phi): return p if self.wAt(phi) else (p + 1) % self.m(r) if self.m(r) else p + 1  # Lean: n % 0 = n
    def edgeOK(self, phi, s, s2):
        phi2 = (phi + 1) % self.P
        r = self.rk(phi, s)
        r2 = self.rk(phi2, s2)
        if not r2 <= r: return False
        if r2 != r: return True
        head = s[0] if s else False
        return self.ps(phi2, s2) == self.nextPos(r, self.ps(phi, s), phi) and (self.wAt(phi) or head == self.u(r, self.ps(phi, s)))
    def check(self):
        bad = []
        for phi in range(self.P):
            for s in all_lists(self.b):
                for x in (False, True):
                    s2 = lin3([self.wAt(phi)] + s + [x])
                    if not self.edgeOK(phi, s, s2): bad.append((phi, s, x))
        return bad
    def checkG(self):
        bad = []
        for r in range(self.nranks):
            mr = self.m(r)
            if not mr > 0: bad.append(('m0', r)); continue
            for p in range(mr):
                for phi in range(self.P):
                    q = (p, phi)
                    for _ in range(mr * self.P):
                        q = (self.nextPos(r, q[0], q[1]), (q[1] + 1) % self.P)
                    if q != (p, phi): bad.append(('G', r, p, phi))
        for phi in range(self.P):
            for s in all_lists(self.b):
                if not self.rk(phi, s) < self.nranks: bad.append(('rk', phi, s))
                elif not self.ps(phi, s) < self.m(self.rk(phi, s)): bad.append(('ps', phi, s))
        return bad

if __name__ == '__main__':
    for name in sys.argv[1:]:
        c = C(parse_inst(name))
        b1 = c.check(); b2 = c.checkG()
        ranks_used = set(c.rk(phi, s) for phi in range(c.P) for s in all_lists(c.b))
        ms = sorted(set(c.m(r) for r in ranks_used))
        print(name, 'w=' + ''.join('1' if x else '0' for x in c.w), 'b=%d' % c.b, 'P=%d' % c.P,
              'nodes=%d' % (c.P << c.b), 'nranks=%d' % c.nranks, 'ranks_used=%d' % len(ranks_used),
              'check_fail=%d' % len(b1), 'checkG_fail=%d' % len(b2), 'periods_used=%s' % ms[:20])
        if b1: print('  first check failures', b1[:5])
        if b2: print('  first checkG failures', b2[:5])
