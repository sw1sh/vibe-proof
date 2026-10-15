# Control: the driven-equivalence check must FAIL for wrong drivers (0, and c & ~c(t+1)),
# and pass for the original driver c and for c' = c & c(t+1).
import importlib.util, sys
N = 400; W = N + 3
def evolve(row0, N):
    rows = [row0[:]]; r = row0
    for _ in range(N):
        n = [0]*len(r)
        for i in range(len(r)):
            l = r[i-1] if i > 0 else 0; c = r[i]; rr = r[i+1] if i+1 < len(r) else 0
            n[i] = l ^ (c | rr)
        rows.append(n); r = n
    return rows
row0 = [0]*(2*W+1); row0[W] = 1
rows = evolve(row0, N+1)
col = lambda t, p: rows[t][p+W]
def drv_ok(dfun, T=0):
    s = [col(T, p) for p in range(-W, 0)]
    for t in range(T, N):
        d = dfun(t); n = [0]*W
        for j in range(W):
            l = s[j-1] if j > 0 else 0; c = s[j]; r = s[j+1] if j+1 < W else d
            n[j] = l ^ (c | r)
        s = n
        if any(s[p+W] != col(t+1, p) for p in range(-W, 0)): return ('fail at t+1 =', t+1)
    return True
print('driver c       :', drv_ok(lambda t: col(t, 0)))
print("driver c'      :", drv_ok(lambda t: col(t, 0) & col(t+1, 0)))
print('driver 0       :', drv_ok(lambda t: 0))
print('driver c&~c+1  :', drv_ok(lambda t: col(t, 0) & (1 - col(t+1, 0))))
print('#t with c=1,c(t+1)=0 (t<N):', sum(1 for t in range(N) if col(t,0)==1 and col(t+1,0)==0))
