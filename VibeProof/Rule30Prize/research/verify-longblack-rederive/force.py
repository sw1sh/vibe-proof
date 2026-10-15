# Black-run forcing: right half cells 1..n at time s arbitrary; boundary cell(t,0)=1 for t=s..s+k-1.
# After k steps, are (cell(s+k,1), cell(s+k,2)) forced?  Exhaustive over the light cone.
import itertools, sys
def step(bnd, row):
    # row = [cell(t,1), ..., cell(t,m)]; returns [cell(t+1,1..m-1)]
    full = [bnd] + row
    return [full[i-1] ^ (full[i] | full[i+1]) for i in range(1, len(row))]
for k in range(1, 13):
    n = k + 2  # cells 1..k+2 needed for cell(s+k,2)
    outs = set()
    for bits in itertools.product((0,1), repeat=n):
        row = list(bits)
        for _ in range(k):
            row = step(1, row)
        outs.add(tuple(row[:2]))
    print(k, sorted(outs))
