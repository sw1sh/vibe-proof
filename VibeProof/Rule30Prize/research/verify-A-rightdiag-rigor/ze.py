# Independent recomputation of z_e (zeros immediately left of right edge in row 2^e), rule 30 single seed.
# Row stored as Python int; bit (p + N) = cell(t, p). Rule 30: new(p) = old(p-1) xor (old(p) or old(p+1)).
import sys, time
E = int(sys.argv[1]); T = 1 << E; N = T + 8
x = 1 << N
z = []; e = 0; t0 = time.time()
for t in range(T + 1):
    if t == (1 << e):
        assert (x >> (N + t)) & 1 == 1 and (x >> (N + t + 1)) == 0  # right edge at p = t
        b = N + t - 1; cnt = 0
        while not (x >> b) & 1:
            cnt += 1; b -= 1
        z.append(cnt); e += 1
    if t == T: break
    x = (x << 1) ^ (x | (x >> 1))
print("z_e:", z, "time %.1fs" % (time.time() - t0))
ej = list(map(int, "0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18 19 20 20 21 21 21 22 23 23 23 24 24 25 25 25 26 27 27 28 28 28 29 30 30 31 31 32".split()))
assert len(ej) == 75
cnt = [sum(1 for j in range(1, 75) if ej[j] <= e) for e in range(len(z))]
print("#{j>=1: e_j<=e}:", cnt)
print("claimed:", [0,2,3,5,6,8,14,15,23,24,26,28,33,35,36,38,40,42,47])
print("match computed vs count:", cnt == z, " match computed vs claimed:", z == [0,2,3,5,6,8,14,15,23,24,26,28,33,35,36,38,40,42,47][:len(z)])
