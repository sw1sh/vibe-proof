# For each column-1 word b (right half driven by alternating c, c(0)=0), compute a = c(t+1) xor (c(t) or b(t)),
# then the left-permutive extension; print the time-0 row x_{-1..-n}(0) and more.
import sys, subprocess
L = int(sys.argv[1]); w = sys.argv[2]; ph0 = int(sys.argv[3])
words = subprocess.run(['./col1words', str(L), w, str(ph0)], capture_output=True, text=True).stdout.split()
p = len(w)
def ext(b):
    n = len(b)
    c = [int(w[(ph0 + t) % p]) for t in range(n + 1)]
    a = [c[t+1] ^ (c[t] | b[t]) for t in range(n)]
    cols = [c[:n], a]
    while len(cols[-1]) > 1:
        xp, xq = cols[-1], cols[-2]
        cols.append([xp[t+1] ^ (xp[t] | xq[t]) for t in range(len(xp) - 1)])
    return cols
for wd in sorted(words):
    b = [int(ch) for ch in wd]
    cols = ext(b)
    row0 = ''.join(str(cols[k][0]) for k in range(1, len(cols)))  # x_{-1}(0), x_{-2}(0), ...
    row1 = ''.join(str(cols[k][1]) for k in range(1, len(cols)-1))
    print(wd, ' row0(-1..):', row0, ' row1:', row1)
