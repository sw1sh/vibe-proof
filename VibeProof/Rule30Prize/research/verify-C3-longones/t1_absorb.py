# Exhaustive check of C2 (absorb): with the center (column 0) black for k consecutive steps,
# which (col1, col2) values are possible after k steps, over ALL contents of columns 1..k+2?
# Independent re-implementation, rule30: new(p) = old(p-1) xor (old(p) or old(p+1)).
import itertools

def rule(a, b, c):
    return a ^ (b | c)

def run(window, centers):
    # window: list of values at columns 1..n at time t; centers: column-0 values at t, t+1, ...
    w = list(window)
    for c0 in centers:
        left = [c0] + w[:-1]          # column p-1 for p = 1..n
        # new values for columns 1..n-1 (last needs column n+1 unknown)
        w = [rule(left[i], w[i], w[i+1]) for i in range(len(w)-1)]
    return w

for k in range(1, 14):
    n = k + 2
    outs = set()
    for bits in itertools.product((0, 1), repeat=n):
        out = run(bits, [1]*k)
        assert len(out) == 2
        outs.add(tuple(out))
    print(f"k={k:2d}: possible (col1,col2) after k black center steps: {sorted(outs)}")

# The exact claim: k=9 -> only (0,1)
outs9 = set(tuple(run(b, [1]*9)) for b in itertools.product((0,1), repeat=11))
print("C2 (k=9) holds exhaustively:", outs9 == {(0,1)})
# Also check: once (0,1), a black center keeps (0,1) -- absorb_stay -- with any col3
for c3 in (0,1):
    w = run([0,1,c3], [1])
    print("absorb_stay with col3 =", c3, "->", w, "(expect [0, 1] for cols 1,2)")
