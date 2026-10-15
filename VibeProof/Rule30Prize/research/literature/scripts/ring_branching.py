# Rule 30 on a ring of size L from a single black cell: every column is eventually periodic,
# yet the fraction of updates with (center=1 and right=1) -- Das's "randomness count" event --
# stays bounded away from 0 on the cycle. Refutes "positive branching frequency => aperiodic".
def step(row):
    L=len(row)
    return [row[(i-1)%L] ^ (row[i] | row[(i+1)%L]) for i in range(L)]
for L in [5,7,9,11,13,17,19,21,25]:
    row=[0]*L; row[L//2]=1
    seen={}; t=0; hist=[]
    while tuple(row) not in seen:
        seen[tuple(row)]=t; hist.append(row); row=step(row); t+=1
    start=seen[tuple(row)]; period=t-start
    cyc=hist[start:]
    br=sum(1 for r in cyc for i in range(L) if r[i]==1 and r[(i+1)%L]==1)
    frac=br/(period*L)
    col=[r[L//2] for r in cyc]
    print(f"L={L:3d} transient={start:4d} period={period:5d} branching fraction on cycle={frac:.4f} center ones fraction={sum(col)/period:.3f}")
