# Brute-force sanity checks of R_period_iff, right_end_copy, and the "in particular" statements.
import sys, time
E = int(sys.argv[1]); TM = 1 << E; N = TM + 8
rows = []; x = 1 << N
for t in range(TM):
    rows.append(x); x = (x << 1) ^ (x | (x >> 1))
def cell(t, p): return (rows[t] >> (p + N)) & 1
def R(j, t): return cell(t, t - j)
# z_e
z = {}
for e in range(E):
    P = 1 << e; c = 0
    while cell(P, P - 1 - c) == 0: c += 1
    z[e] = c
print("z:", [z[e] for e in range(E)])
# 1. iff (finite-window LHS) for e <= E-2, J <= 45
JMAX = 45
Rcols = [[R(j, t) for t in range(TM)] for j in range(JMAX + 1)]
bad = 0; decisive_bad = 0
for e in range(E - 1):
    P = 1 << e
    perj = [all(Rcols[j][t + P] == Rcols[j][t] for t in range(TM - P)) for j in range(JMAX + 1)]
    for J in range(JMAX + 1):
        lhs = all(perj[:J + 1]); rhs = all(cell(P, P - j) == 0 for j in range(1, J + 1))
        if lhs != rhs: bad += 1
        if (lhs and J > z[e]) or ((not lhs) and J <= z[e]): decisive_bad += 1
print("iff mismatches (window):", bad, " z-characterization mismatches:", decisive_bad)
# 2. copy identity cell(t+m*2^e, p+m*2^e) = cell(t,p) for 0 <= t-p <= z_e
viol = 0; checks = 0
for e in range(E - 1):
    P = 1 << e
    for m in range(1, 4):
        for t in range(0, TM - m * P):
            for d in range(0, z[e] + 1):
                p = t - d; checks += 1
                if cell(t + m * P, p + m * P) != cell(t, p): viol += 1
print("copy checks:", checks, "violations:", viol)
# 2b. Does the copy identity fail at d = z_e + 1 (sharpness)? count failures
sharp = []
for e in range(E - 1):
    P = 1 << e; d = z[e] + 1
    fails = sum(1 for t in range(0, TM - P) if cell(t + P, t - d + P) != cell(t, t - d))
    sharp.append(fails)
print("failures at d=z_e+1 (m=1), per e:", sharp)
# 3. row 2^e+s ends with 0^(z_e-2s) then row s; also check maximality of the zero run
v3 = 0; maxrun_ok = 0; maxrun_tot = 0
for e in range(E - 1):
    P = 1 << e
    for s in range(0, z[e] // 2 + 1):
        if P + s >= TM: continue
        tail = [cell(P + s, q) for q in range(P + s - z[e], P + s + 1)]
        want = [0] * (z[e] - 2 * s) + [cell(s, q) for q in range(-s, s + 1)]
        if tail != want: v3 += 1
        maxrun_tot += 1
        if cell(P + s, P + s - z[e] - 1) == 1: maxrun_ok += 1
print("row-copy violations:", v3, " zero-run maximal in", maxrun_ok, "of", maxrun_tot)
# 4. column 2^e reproduces c(0..z_e) at times 2^e..2^e+z_e
v4 = 0
for e in range(E - 1):
    P = 1 << e
    for t in range(0, z[e] + 1):
        if cell(P + t, P) != cell(t, 0): v4 += 1
print("column violations:", v4)
# 5. least periods e_j for j where decisive (true period 2^a <= TM guaranteed when j <= E)
ej_brief = list(map(int, "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18".split()))
ej = []
for j in range(JMAX + 1):
    found = None
    for e in range(E):
        P = 1 << e
        if all(Rcols[j][t + P] == Rcols[j][t] for t in range(TM - P)): found = e; break
    ej.append(found)
print("e_j computed (window 2^%d):" % E, ej)
print("agree with brief for j<=%d:" % JMAX, [j for j in range(JMAX + 1) if ej[j] != ej_brief[j]] == [])
