# Independent re-check of the packed certificates in the Lean instance files.
# Written from the claim's statement, not from cert.py / export_cert.py.
# Edge relation computed column-by-column with rule 30 (new = left xor (center or right)).
import re, sys
sys.set_int_max_str_digits(0)
def parse(path):
    src = open(path).read()
    def nat(name):
        m = re.search(rf"def \w+_{name} : Nat := (\d+)", src); return int(m.group(1))
    m = re.search(r"def \w+_w : List Bool := \[([^\]]*)\]", src)
    w = [x.strip() == "true" for x in m.group(1).split(",")]
    return w, nat("b"), nat("nranks"), nat("rankP"), nat("posP"), nat("perP"), nat("wordP")
def run(path):
    w, b, nr, rankP, posP, perP, wordP = parse(path)
    P = len(w)
    # unpack tables once (big-int shifting is slow, so slice via bytes)
    N = P << b
    rb = rankP.to_bytes((rankP.bit_length() + 7) // 8 + 2 * N + 8, "little")
    pb = posP.to_bytes((posP.bit_length() + 7) // 8 + N + 8, "little")
    rank = [rb[2 * i] | (rb[2 * i + 1] << 8) for i in range(N)]
    pos = [pb[i] for i in range(N)]
    mb = perP.to_bytes((perP.bit_length() + 7) // 8 + nr + 8, "little")
    per = [mb[r] for r in range(nr)]
    def u(r, p): return (wordP >> (64 * r + p)) & 1
    def idx(phi, s): return phi * (1 << b) + s          # s: bit (i-1) = column i  (little-endian enc)
    def col(s, i): return (s >> (i - 1)) & 1
    def step(c0, s, x):
        cols = [c0] + [col(s, i) for i in range(1, b + 1)] + [x]
        ns = 0
        for i in range(1, b + 1):
            ns |= (cols[i - 1] ^ (cols[i] | cols[i + 1])) << (i - 1)
        return ns
    errs = 0; npres = 0
    for r in range(nr):
        if per[r] == 0: errs += 1
    for phi in range(P):
        white = not w[phi]
        for s in range(1 << b):
            i = idx(phi, s); r = rank[i]
            if not (r < nr): errs += 1; continue
            if not (pos[i] < per[r]): errs += 1
            for x in (0, 1):
                t = step(int(w[phi]), s, x); j = idx((phi + 1) % P, t)
                if rank[j] > r: errs += 1; continue
                if rank[j] == r:
                    npres += 1
                    m = per[r]
                    want = (pos[i] + 1) % m if white else pos[i]
                    if pos[j] != want: errs += 1
                    if white and col(s, 1) != u(r, pos[i]): errs += 1
    # G^{mP} = id on [0,m) x [0,P): count of whites in one period times m is 0 mod m (check directly anyway)
    z = sum(1 for x in w if not x)
    for r in range(nr):
        m = per[r]
        if m == 0: continue
        for p in range(m):
            for phi in range(P):
                q = (p, phi)
                for _ in range(m * P):
                    q = ((q[0] + (0 if w[q[1]] else 1)) % m, (q[1] + 1) % P)
                if q != (p, phi): errs += 1
    words = sorted(set("".join(str(u(r, p)) for p in range(per[r])) for r in set(rank)))
    print(path.split("/")[-1], "w=" + "".join("1" if x else "0" for x in w), "b=%d" % b, "P=%d" % P,
          "nodes=%d" % N, "ranks used=%d" % len(set(rank)), "rank-preserving edges=%d" % npres,
          "periods=%s" % sorted(set(per[r] for r in set(rank))), "words=%s" % words, "ERRORS=%d" % errs)
for p in sys.argv[1:]: run(p)
