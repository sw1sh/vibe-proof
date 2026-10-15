# Abstract check: c = (01)^inf (zeros at even times), e(t) = 1 at odd t, e(t) = [t in S] at even t, S = {2^k : k>=1}.
# Window comparison of window_jen: for t1 < t2 with t1 = t2 mod 2 (so c-windows agree), do the e-windows of length t2 differ?
import sys
N = int(sys.argv[1])
S = set(2**k for k in range(1, 40))
e = [1 if t % 2 else (1 if t in S else 0) for t in range(3 * N)]
bad = []
for t2 in range(1, N):
    for t1 in range(t2 % 2, t2, 2):
        if e[t1:t1 + t2] == e[t2:2 * t2]:
            bad.append((t1, t2))
            break
print('pairs with equal windows (t1<t2<=N):', len(bad), bad[:10])
# compare with a sparser set S' = {3^k}: expect equal windows to exist (contradiction available)
S3 = set(2 * 3**k for k in range(0, 25))
e3 = [1 if t % 2 else (1 if t in S3 else 0) for t in range(3 * N)]
cnt = 0; ex = None
for t2 in range(1, N):
    for t1 in range(t2 % 2, t2, 2):
        if e3[t1:t1 + t2] == e3[t2:2 * t2]:
            cnt += 1; ex = ex or (t1, t2); break
print('S = 2*3^k: t2 values having an equal earlier window:', cnt, 'first', ex)
