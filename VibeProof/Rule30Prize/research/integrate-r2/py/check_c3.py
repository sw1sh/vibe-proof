import itertools
def rule(a,b,c): return a ^ (b | c)
def run_left(s, drv, T):
    # s: list, s[k-1] = cell at -k (k=1..W); returns column -1 values for t in 0..T
    W = len(s) + T + 3
    row = [0]*(W+2)   # index k = depth, k=0 is boundary
    for k,v in enumerate(s, start=1): row[k] = v
    out = []
    for t in range(T+1):
        out.append(row[1])
        new = [0]*(W+2)
        for k in range(1, W+1):
            right = drv[t % 4] if k == 1 else row[k-1]
            new[k] = rule(row[k+1], row[k], right)
        row = new
    return out
words = {'0001': ('0000', [0,None,0,1]), '0011': ('0010', [None,0,0,1]), '0111': ('0110', [None,0,0,1])}
for w,(ce,P) in words.items():
    drv = [int(ch) for ch in ce]
    # effective boundary check
    wb = [int(ch) for ch in w]
    eff = [wb[i] & wb[(i+1)%4] for i in range(4)]
    print(w, "eff", eff, "given", drv)
    # zero config
    col = run_left([], drv, 400)
    def fits(col, start):
        return all(P[t%4] is None or col[t]==P[t%4] for t in range(start, len(col)))
    print("  zero config fits from 100:", fits(col, 100), col[:16])
    # small configs
    cnt = 0; tot = 0
    for W in range(1, 8):
        for bits in itertools.product([0,1], repeat=W):
            if bits[-1] == 0: continue
            tot += 1
            col = run_left(list(bits), drv, 160)
            if fits(col, 80): cnt += 1
    print("  configs (W<=7, nonzero) fitting P on [80,160]:", cnt, "of", tot)
