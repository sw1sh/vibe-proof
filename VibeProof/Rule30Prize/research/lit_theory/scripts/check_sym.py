import sys
fts = [int(l.split('ftab=')[1].split()[0], 16) for l in open(sys.argv[1])]
def rev5(w): return int(format(w, '05b')[::-1], 2)
def sim(ft, T):
    W = 4*T + 8; off = 2*T + 4
    row = [0]*W; row[off] = 1
    c = []
    for t in range(T):
        c.append(row[off])
        new = [0]*W
        lo, hi = off - 2*t - 2, off + 2*t + 2
        for i in range(lo, hi+1):
            w = (row[i-2]<<4)|(row[i-1]<<3)|(row[i]<<2)|(row[i+1]<<1)|row[i+2]
            new[i] = (ft >> w) & 1
        row = new
    return c
for ft in fts:
    sym = all(((ft>>w)&1) == ((ft>>rev5(w))&1) for w in range(32))
    rp = all(((ft>>w)&1) != ((ft>>(w^1))&1) for w in range(32) if not (w&1))  # permutive in rightmost var e
    pal = set(((ft>>w)&1, (w>>2)&1) for w in range(32) if w == rev5(w))  # (f, center) on palindromic windows
    c = sim(ft, 700)
    print(hex(ft), "reflection-symmetric" if sym else "asymmetric", "right-permutive" if rp else "not-right-permutive",
          "f vs center on palindromes:", sorted(pal), "center col first 40:", ''.join(map(str, c[:40])), "tail const:", len(set(c[100:])) == 1)
