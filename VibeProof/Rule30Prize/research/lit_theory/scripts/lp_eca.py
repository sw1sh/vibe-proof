# For each elementary CA rule, simulate from a single 1 and test columns for eventual periodicity
# (heuristic: period P <= Pmax with transient <= T/2 over T steps).
import sys
T = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
def run(rule, T):
    W = T + 2
    row = [0]*(2*W+1); row[W] = 1
    cols = {p: [] for p in range(-3, 4)}
    for t in range(T):
        for p in cols: cols[p].append(row[W+p])
        new = [0]*(2*W+1)
        for i in range(1, 2*W):
            a, b, c = row[i-1], row[i], row[i+1]
            new[i] = (rule >> (4*a+2*b+c)) & 1
        row = new
    return cols
def evper(seq, Pmax):
    n = len(seq)
    for P in range(1, Pmax+1):
        # find minimal transient
        ok = True
        Tt = n//2
        if all(seq[t] == seq[t+P] for t in range(Tt, n-P)):
            return P
    return None
def is_left_perm(rule):
    f = lambda a,b,c: (rule >> (4*a+2*b+c)) & 1
    return all(f(0,b,c) != f(1,b,c) for b in (0,1) for c in (0,1))
def is_right_perm(rule):
    f = lambda a,b,c: (rule >> (4*a+2*b+c)) & 1
    return all(f(a,b,0) != f(a,b,1) for a in (0,1) for b in (0,1))
rules = [r for r in range(256) if is_left_perm(r) and (r & 1) == 0]
for r in rules:
    cols = run(r, T)
    res = {p: evper(cols[p], 200) for p in cols}
    print(r, 'RP' if is_right_perm(r) else '  ', 'f001=%d' % ((r>>1)&1), ' '.join('%d:%s' % (p, res[p]) for p in sorted(res)))
