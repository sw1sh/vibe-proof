# Verify Nersissian's support recurrence S_m = Inc(S_{m-1} ^ S_{m-2} ^ (S_{m-1} OR-conv S_{m-2})), min S_m = floor(m/2),
# max S_m <= F_{m+1}-1, and that E(S_m)(n) equals rule 30 right diagonal b(m,n)=A(n,n-m+1), period = 2^ceil(log2(max S_m+1)).
import sys
M = int(sys.argv[1]) if len(sys.argv) > 1 else 26

def or_conv(A, B):
    out = set()
    from collections import Counter
    cnt = Counter()
    for a in A:
        for b in B:
            cnt[a | b] ^= 1
    return {c for c, v in cnt.items() if v}

S = {1: {0}, 2: {1}}
for m in range(3, M + 1):
    tilde = S[m-1] ^ S[m-2] ^ or_conv(S[m-1], S[m-2])
    S[m] = {a + 1 for a in tilde}

# simulate rule 30 enough steps
T = 1 << 12
W = 2*T + 5; off = T + 2; mask = (1 << W) - 1
x = 1 << off
rows = []
for t in range(T):
    rows.append(x)
    x = (((x << 1) & mask) ^ (x | (x >> 1))) & mask
def cell(t, p):
    return (rows[t] >> (p + off)) & 1

def lucas_eval(Sset, n):
    return sum(1 for r in Sset if (r & n) == r) & 1

F = [0, 1]
while len(F) < M + 5: F.append(F[-1] + F[-2])
ok = True
for m in range(1, M + 1):
    Sm = S[m]
    mn, mx = min(Sm), max(Sm)
    if mn != m // 2: ok = False; print('min fail', m, mn)
    if mx > F[m+1] - 1: ok = False; print('fib fail', m, mx, F[m+1]-1)
    # compare values for n < 2^k window and up to T
    for n in range(0, min(T, 1500)):
        if lucas_eval(Sm, n) != cell(n, n - m + 1):
            ok = False; print('value mismatch', m, n); break
    k = (mx).bit_length()  # minimal k with S subset [0,2^k)
    per = 1 << k
    # least period of diagonal from data (purely periodic from 0)
    seq = [cell(n, n - m + 1) for n in range(min(T, 4 * per + 64))] if per <= T // 4 else None
    lp = None
    if seq:
        for p in range(1, len(seq)//2):
            if all(seq[i] == seq[i+p] for i in range(len(seq)-p)):
                lp = p; break
    print(f'm={m:2d} j={m-1:2d} |S|={len(Sm):6d} minS={mn:3d} maxS={mx:6d} F_(m+1)-1={F[m+1]-1:7d} period_from_support=2^{k} least_period_data={lp}')
print('ALL OK' if ok else 'FAILURES')
