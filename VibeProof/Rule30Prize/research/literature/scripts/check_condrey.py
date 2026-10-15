# Sanity-check Condrey 2026 Theorems 2 and 3 numerically on a finite window.
import random
def step(row):
    # row: dict-free list over positions [-N..N]; boundary cells treated as given by extension functions
    n=len(row)
    new=[0]*n
    for i in range(1,n-1):
        new[i]=row[i-1]^(row[i]|row[i+1])
    return new
def run(Lfun, Rfun, x0, N, T):
    # positions -N..N, index i -> pos i-N
    row=[0]*(2*N+1)
    for j in range(1,N+1):
        row[N-j]=Lfun(j)
        row[N+j]=Rfun(j)
    row[N]=x0
    trace=[row[N]]
    # valid region shrinks by 1 each side per step; keep T << N
    for t in range(T):
        row=step(row)
        trace.append(row[N])
    return trace
random.seed(1)
N=400; T=300
ok=True
for trial in range(200):
    m=random.randint(1,8)
    Rbits={j:(1 if j==m else (0 if j<m else random.randint(0,1))) for j in range(1,N+1)}
    R=lambda j: Rbits[j]
    L=lambda j: 0 if j<m else (1 if j==m else j%2)
    tr=run(L,R,0,N,T)
    if any(tr): ok=False; print('Thm2 fail m=',m, tr[:40]); break
print('Theorem 2 (zero-trace fiber) holds on', 'all trials' if ok else 'NOT all trials')
ok=True
for trial in range(200):
    Rbits={j:random.randint(0,1) for j in range(1,N+1)}
    R=lambda j: Rbits[j]
    L=lambda j: 1 if (j>0 and j%2==0) else 0
    tr=run(L,R,1,N,T)
    if not all(tr): ok=False; print('Thm3 fail', tr[:40]); break
print('Theorem 3 (all-one fiber) holds on', 'all trials' if ok else 'NOT all trials')
# Check horizon table of Thm 6/7 for small w by brute force
def horizon(x,w,const):
    N=w+3*w+10
    row=[0]*(2*N+1)
    for p in range(-w,w+1): row[N+p]=x[p+w]
    h=-1
    for t in range(0,4*w+10):
        if row[N]!=const: break
        h=t
        row=step(row)
    return h
for w in range(1,8):
    best0=-1;c0=0;best1=-1;c1=0
    for mask in range(1<<(2*w+1)):
        x=[(mask>>k)&1 for k in range(2*w+1)]
        if x[w]==0:
            if mask==0: continue
            h=horizon(x,w,0)
            if h>best0: best0,c0=h,1
            elif h==best0: c0+=1
        else:
            h=horizon(x,w,1)
            if h>best1: best1,c1=h,1
            elif h==best1: c1+=1
    print('w',w,'H0',best0,c0,'H1',best1,c1)
