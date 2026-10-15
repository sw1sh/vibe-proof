# b3: right half driven by alternating column (white first at time 0): col1 at times 0,2,4,6,8 never all white
import itertools
def rule(a,b,c): return a ^ (b | c)
def col1_vals(row, cs):
    # row = columns 1..n at time 0 ; cs = center values at times 0..len(cs)-1
    out = []
    r = list(row)
    for c in cs:
        out.append(r[0])
        new = []
        for i in range(len(r)-1):
            left = c if i == 0 else r[i-1]
            new.append(rule(left, r[i], r[i+1]))
        r = new
    return out
cs = [i % 2 for i in range(9)]  # white first: 0,1,0,1,...
bad = 0
for bits in itertools.product([0,1], repeat=11):
    v = col1_vals(bits, cs)
    if not (v[0] or v[2] or v[4] or v[6] or v[8]): bad += 1
print("b3 counterexamples with 11 cells:", bad)
# with 4 white steps only
bad4 = 0
for bits in itertools.product([0,1], repeat=11):
    v = col1_vals(bits, cs[:7])
    if not (v[0] or v[2] or v[4] or v[6]): bad4 += 1
print("4 white steps all white possible:", bad4)
