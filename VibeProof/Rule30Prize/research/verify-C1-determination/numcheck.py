import random, sys
def evolve(row0, T):
    # row0: dict-free list on fixed width with zero padding wide enough; returns list of rows
    rows=[row0]
    W=len(row0)
    for t in range(T):
        r=rows[-1]
        nr=[0]*W
        for p in range(W):
            l=r[p-1] if p>0 else 0
            c=r[p]
            rr=r[p+1] if p+1<W else 0
            nr[p]=l ^ (c | rr)
        rows.append(nr)
    return rows
def check(rows, T, cols, mmax, label):
    tested=0; hyp=0
    for i in cols:
        for m in range(0, mmax+1):
            # bucket times by (column i window, orCol window)
            buckets={}
            for t in range(0, T-m):
                key=(tuple(rows[t+s][i] for s in range(m+1)),
                     tuple(rows[t+s][i] | rows[t+s][i+1] for s in range(m)))
                tri=tuple(rows[t+s][i-k] for k in range(m+1) for s in range(m+1-k))
                if key in buckets:
                    hyp+=1
                    if buckets[key]!=tri:
                        print("COUNTEREXAMPLE", label, i, m, t); sys.exit(1)
                else:
                    buckets[key]=tri
                tested+=1
    print(label, "windows tested", tested, "repeat-key comparisons", hyp, "no counterexample")
# single black cell, width big enough for T steps (lightcone), column offset
T=600; off=T+5; W=2*T+10
row=[0]*W; row[off]=1
rows=evolve(row,T)
check(rows, T, [off+d for d in range(-40,41,4)], 9, "single-cell")
random.seed(1)
for trial in range(3):
    W=900
    row=[random.randint(0,1) for _ in range(W)]
    rows=evolve(row,300)
    # stay away from the boundary-affected region: boundary effects travel 1 cell/step;
    # columns near center with T=300 and W=900 are unaffected
    check(rows, 300, list(range(430,470,3)), 8, "random-ic-%d"%trial)
