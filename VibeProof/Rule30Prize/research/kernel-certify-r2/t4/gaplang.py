# Which gap words occur along paths inside the bad SCC (w = 01), via subset simulation.
import sys, itertools
exec(open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t4/badscc.py').read().split('w = sys.argv[1]')[0])
from collections import deque, defaultdict
def bad_class(w, b):
    P = len(w)
    def succs(phi, s):
        c = int(w[phi]); bit = lambda p: c if p == 0 else (s >> (p - 1)) & 1
        base = 0
        for p in range(1, b): base |= (bit(p - 1) ^ (bit(p) | bit(p + 1))) << (p - 1)
        nphi = (phi + 1) % P
        return sorted(set((nphi, base | ((bit(b - 1) ^ (bit(b) | x)) << (b - 1))) for x in (0, 1)))
    return succs
def occurs(B, succs, w, pat):
    P = len(w); fph = w.index('0')
    cur = set(v for v in B if v[0] == fph and (v[1] & 1) == pat[0])
    for y in pat[1:]:
        nx = set()
        for v in cur:
            fr = {v}
            for _ in range(P): fr = set(u for x in fr for u in succs(*x) if u in B)
            nx |= fr
        cur = set(v for v in nx if (v[1] & 1) == y)
        if not cur: return False
    return True
def gp(gs): return [1] + sum(([0] * g + [1] for g in gs), [])
w = sys.argv[1]
for b in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
    # recover the bad class with the same procedure as badscc.analyze
    import types
    P = len(w); succs = bad_class(w, b)
    nodes = [(phi, s) for phi in range(P) for s in range(1 << b)]
    # reuse analyze internals: recompute bad set
    res = analyze(w, b, 2, 1)
    # get B again (analyze does not return it); quick recompute via same code path
    src = open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t4/badscc.py').read()
    ns = {}
    exec(src.split('w = sys.argv[1]')[0].replace("    res = {'b': b, 'nbad': len(bads)}", "    return set(members[bads[0]]) if len(bads)==1 else None\n    res = {}"), ns)
    B = ns['analyze'](w, b)
    occ1 = [g for g in range(0, 8) if occurs(B, succs, w, gp([g]))]
    out = {'b': b, 'size': len(B), 'single gaps occurring': occ1}
    alph = [g for g in occ1 if g >= 1]
    for k in (2, 3):
        forb = []
        for t in itertools.product(alph, repeat=k):
            if not occurs(B, succs, w, gp(list(t))):
                if k == 2 or (occurs(B, succs, w, gp(list(t[1:]))) and occurs(B, succs, w, gp(list(t[:-1])))):
                    forb.append(''.join(map(str, t)))
        out[f'minimal forbidden {k}'] = forb
    print(out, flush=True)
