# Check hand-derived forced/affine structure of left columns for period-3 words.
# Left reconstruction: col[j+1](t) = col[j](t+1) xor (col[j](t) or col[j-1](t)), col[0] = effective boundary c' = c & sigma c.
import random
def recon(col0, colm1, depth):
    cols = [col0, colm1]
    for j in range(1, depth):
        a, b = cols[j], cols[j-1]
        n = len(a) - 1
        cols.append([a[t+1] ^ (a[t] | b[t]) for t in range(n)])
    return cols
def check(word, pattern, formulas, trials=200):
    P = len(word)
    ceff = [word[i] & word[(i+1) % P] for i in range(P)]
    for _ in range(trials):
        K = 40
        s = [random.randint(0,1) for _ in range(K+5)]
        colm1 = []
        for k in range(K):
            for ph in range(P):
                v = pattern[ph]
                colm1.append(s[k] if v == '*' else int(v))
        col0 = [ceff[t % P] for t in range(len(colm1))]
        cols = recon(col0, colm1, 8)
        for j, f in formulas.items():
            for k in range(10):
                for ph in range(P):
                    t = P*k + ph
                    if cols[j][t] != f[ph](s, k):
                        return f"FAIL word={word} col=-{j} k={k} ph={ph}"
    return "ok"
N = lambda x: 1 - x
f001 = {
 1: [lambda s,k: 0, lambda s,k: s[k], lambda s,k: 1],
 2: [lambda s,k: s[k], lambda s,k: N(s[k]), lambda s,k: 1],
 3: [lambda s,k: 1, lambda s,k: 0, lambda s,k: N(s[k+1])],
 4: [lambda s,k: 1, lambda s,k: s[k]^s[k+1], lambda s,k: 0],
 5: [lambda s,k: N(s[k]^s[k+1]), lambda s,k: s[k]^s[k+1], lambda s,k: s[k+1]],
 6: [lambda s,k: N(s[k]^s[k+1]), lambda s,k: s[k], lambda s,k: N(s[k+2])],
}
f011 = {
 1: [lambda s,k: s[k], lambda s,k: 0, lambda s,k: 1],
 2: [lambda s,k: s[k], lambda s,k: 0, lambda s,k: N(s[k+1])],
 3: [lambda s,k: s[k], lambda s,k: N(s[k+1]), lambda s,k: N(s[k+1])],
 4: [lambda s,k: s[k]^N(s[k+1]), lambda s,k: 0, lambda s,k: 1],
}
print("001", check([0,0,1], "0*1", f001))
print("011", check([0,1,1], "*01", f011))
