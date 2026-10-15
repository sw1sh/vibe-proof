import sys
sys.set_int_max_str_digits(0)
N = int(sys.argv[1])
K = N
row = 1 << K
bits = []
for t in range(N):
    bits.append((row >> K) & 1)
    row = (row << 1) ^ (row | (row >> 1))
C = sum(b << t for t, b in enumerate(bits))
# cross-check against Ruliology's independent C computation (8 values per byte, high bit first)
ref = open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb').read(N // 8 + 1)
refbits = [(ref[t // 8] >> (7 - t % 8)) & 1 for t in range(N)]
print("N =", N, "matches Ruliology center-1e7.bin:", refbits == bits)
# window: for each P in 1..N/4, first witness k >= 0 with c(N/2+k) != c(N/2+k+P)
maxk = 0
for P in range(1, N // 4 + 1):
    k = 0
    while bits[N // 2 + k] == bits[N // 2 + k + P]: k += 1
    maxk = max(maxk, k)
print("max first-witness offset over P <= N/4:", maxk)
open(f'/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/window/C_{N}.txt', 'w').write(str(C))
print("C decimal digits:", len(str(C)))
