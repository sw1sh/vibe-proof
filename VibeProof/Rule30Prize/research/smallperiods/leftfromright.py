# Right half driven by alternating c (c(t)=t%2 pattern from word '01' i.e. c(0)=0), compute column 1 b,
# set a(t) = c(t+1) xor (c(t) or b(t)), extend left (transposed). Show rows of the left half (positions -1..-N) at several times.
import sys, subprocess
W0 = int(sys.argv[1]); steps = int(sys.argv[2]); seed = int(sys.argv[3]); t0 = int(sys.argv[4]); N = int(sys.argv[5]); nrows = int(sys.argv[6])
s = subprocess.run(['./rh', '01', str(W0), str(steps), str(seed), '1'], capture_output=True, text=True).stdout.strip()
b = [int(ch) for ch in s]
c = [t % 2 for t in range(steps + 1)]
a = [c[t+1] ^ (c[t] | b[t]) for t in range(steps)]
# columns as python ints over time: bit t
cols = {0: c[:steps], -1: a}
p = -1
while -p < N + 1:
    xp, xq = cols[p], cols[p+1]
    n = len(xp) - 1
    cols[p-1] = [xp[t+1] ^ (xp[t] | xq[t]) for t in range(n)]
    p -= 1
for t in range(t0, t0 + nrows):
    print('%6d' % t, ''.join('#' if cols[-n][t] else '.' for n in range(N, 0, -1)), '|', c[t])
