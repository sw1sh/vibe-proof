# Diagonals of rule 30 from a single cell, via the exact diagonal recurrences.
# Right: R_j(t) = cell(t, t-j):  R_j(t+1) = R_j(t) ^ (R_{j-1}(t) | R_{j-2}(t)),  R_0 = 1, R_{-1} = R_{-2} = 0
# Left:  D_j(t) = cell(t, j-t):  D_j(t+1) = D_{j-2}(t) ^ (D_{j-1}(t) | D_j(t)),  D_0 = 1, D_{-1} = D_{-2} = 0
import sys
J = 22; L = 1 << 24
def right():
    prev2 = [0] * L; prev1 = [1] * L; out = [prev1]
    for j in range(1, J + 1):
        cur = [0] * L; x = 0
        for t in range(L):
            cur[t] = x; x ^= prev1[t] | prev2[t]
        out.append(cur); prev2, prev1 = prev1, cur
    return out
def left():
    prev2 = [0] * L; prev1 = [1] * L; out = [prev1]
    for j in range(1, J + 1):
        cur = [0] * L; x = 0
        for t in range(L):
            cur[t] = x; x = prev2[t] ^ (prev1[t] | x)
        out.append(cur); prev2, prev1 = prev1, cur
    return out
def eventual(seq, maxT=1 << 22):
    n = len(seq)
    for P in range(1, n // 4):
        # smallest T such that seq is P-periodic on [T, n)
        T = n - P
        while T > 0 and seq[T - 1] == seq[T - 1 + P]: T -= 1
        if T <= n // 2: return T, P
    return None
L = 1 << 18; J = 16
R = right(); D = left()
print("right diagonals (transient, least period):", [eventual(R[j]) for j in range(J + 1)])
print("left  diagonals (transient, least period):", [eventual(D[j]) for j in range(J + 1)])
