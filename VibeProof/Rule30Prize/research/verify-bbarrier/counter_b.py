# Numerical sanity check of a left-only, T-uniform exclusion of the word 1 inside [T, 2T-2].
# D_j(t) = cell(t, j - t) (left diagonals).  Claimed: D_2(t) = 0 for t >= 2, D_4(t) = 1 for t >= 4.
# Under "c = 1 on [T, 2T-2]", forced constraints give cell(t,-1) = 0 on [T, 2T-3]; permutivity then
# forces the time-T left half to equal alt (black iff position even) on -1..-(T-2).
# T even: alt(-(T-2)) = 1 but D_2(T) = 0.  T odd (T >= 5): alt(-(T-4)) = 0 but D_4(T) = 1.

def rule(a, b, d):
    return a ^ (b | d)

N = 700
R = [{0: 1}]
for t in range(N):
    r = R[-1]
    R.append({p: rule(r.get(p - 1, 0), r.get(p, 0), r.get(p + 1, 0)) for p in range(-t - 1, t + 2)})
cell = lambda t, p: R[t].get(p, 0)

print("D_2(t)=0 for 2<=t<=N:", all(cell(t, 2 - t) == 0 for t in range(2, N + 1)))
print("D_4(t)=1 for 4<=t<=N:", all(cell(t, 4 - t) == 1 for t in range(4, N + 1)))

alt = lambda p: 1 if p % 2 == 0 else 0      # p < 0; Python % matches Lean Int.emod here

# Driven left half from the ACTUAL time-T state, driver = 1 (the hypothetical word 1).
def first_violation(T, steps):
    W = T + steps + 3
    row = [0] * (W + 2)
    for i in range(1, T + 1):
        row[i] = cell(T, -i)
    for k in range(steps + 1):
        if row[1] != 0:          # forced: cell(T+k,-1) must be 0 when c(T+k)=c(T+k+1)=1
            return k
        new = [0] * (W + 2)
        for i in range(1, W + 1):
            right = row[i - 1] if i >= 2 else 1
            new[i] = rule(row[i + 1], row[i], right)
        row = new
    return None

worst = 0
ok_mech = True
for T in range(5, 301):
    k = first_violation(T, T - 3)            # steps 0..T-3  <->  times T..2T-3
    assert k is not None and k <= T - 3, (T, k)
    worst = max(worst, k)
    m = T - 2 if T % 2 == 0 else T - 4      # the cell where the actual state must differ from alt
    if cell(T, -m) == alt(-m):
        ok_mech = False
        print("mechanism fails at", T)
print("every T in [5,300]: actual time-T left half violates the word-1 forced constraints by time 2T-3;",
      "largest first-violation step seen:", worst)
print("mechanism (differs from alt at -(T-2) if T even, -(T-4) if T odd) holds:", ok_mech)
