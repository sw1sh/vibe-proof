# Numerical sanity check of claim restart_continuity_black_centers
T = 4096
W = 2 * T + 3
mask = (1 << W) - 1
off = T + 1  # bit index = p + off
rows = []
x = 1 << off
for t in range(T):
    rows.append(x)
    x = ((x << 1) ^ (x | (x >> 1))) & mask

def cell(t, p):
    i = p + off
    if i < 0 or i >= W:
        return 0
    return (rows[t] >> i) & 1

def R(j, t):
    return cell(t, t - j)

c = [cell(t, 0) for t in range(T)]
assert c[:20] == [1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1], c[:20]

def per(j, k):
    P = 1 << k
    return all(R(j, t + P) == R(j, t) for t in range(0, T - P))

# e_j for j <= 26 (periods up to 1024 fully checkable)
e = []
for j in range(27):
    k = 0
    while not per(j, k):
        k += 1
    e.append(k)
print("e_j:", e)
ref = [0,1,1,2,3,3,4,5,5,6,6,6,6,6,6,7,8,8,8,8,8,8,8,8,9,10,10]
assert e == ref[:27]
# monotonicity check (data)
assert all(e[i] <= e[i+1] for i in range(len(e)-1))
# J_k = max{j : e_j <= k}
J = {}
for k in range(10):
    J[k] = max(j for j in range(27) if e[j] <= k)
print("J_k:", [J[k] for k in range(10)])

def nu2(n):
    v = 0
    while n % 2 == 0:
        n //= 2; v += 1
    return v

# (a) general restart: cell(N+s, N+q) == cell(s,q) for 0 <= s-q <= J_{nu2 N}
bad = 0; cnt = 0
for N in range(1, 1200):
    k = min(nu2(N), 9)
    Jk = J[k]
    for s in range(0, T - N):
        for d in range(0, Jk + 1):
            q = s - d
            cnt += 1
            if cell(N + s, N + q) != cell(s, q):
                bad += 1
print("restart general checks:", cnt, "failures:", bad)
# sharpness/flip: for u odd, cell(2^k u + J_k + 1, 2^k u) == 1 - c(J_k+1); u even -> == c(J_k+1)
fl = 0; cntf = 0
for k in range(9):
    for u in range(1, (T - 40) >> k):
        N = (1 << k) * u
        tt = N + J[k] + 1
        if tt >= T: break
        cntf += 1
        expect = (1 - c[J[k] + 1]) if u % 2 == 1 else c[J[k] + 1]
        if cell(tt, N) != expect:
            fl += 1
        for s in range(J[k] + 1):
            if N + s < T and cell(N + s, N) != c[s]:
                fl += 1
print("column repeat/flip checks:", cntf, "failures:", fl)
# (b): c(t)=1 -> R_t not 2^k-periodic for any 2^k <= t (check via t mod 2^k)
viol = 0
hyp_c = []
for t in range(1, T):
    k = 0
    while (1 << k) <= t:
        P = 1 << k
        r = t % P
        # if R_t had period P then R_t(t) = R_t(r) = 0 since 2r < t
        assert 2 * r < t and R(t, r) == 0
        if per(t, k) if t < 27 else False:
            hyp_c.append((t, k))
            if c[t] == 1:
                viol += 1
        k += 1
print("(b) violations:", viol, "; (t,k) with Per t (2^k), 2^k <= t, t<27:", hyp_c)
