# all primitive binary words of length 1..n (each rotation listed separately), excluding all-zero
import sys
n = int(sys.argv[1])
def primitive(w):
    L = len(w)
    return all(w != w[d:] + w[:d] for d in range(1, L) if L % d == 0) if L > 1 else True
out = []
for L in range(1, n + 1):
    for k in range(1 << L):
        w = format(k, '0%db' % L)
        if '1' not in w: continue
        if not primitive(w): continue
        out.append(w)
print(' '.join(out))
