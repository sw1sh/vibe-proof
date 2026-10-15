# Right half (columns p >= 1) driven by c(t) = 1 at even t, 0 at odd t (period 2, phase c(0)=1).
# Bit i of x <-> column i+1. new = left xor (center or right); left of column 1 is c(t).
# For each finite initial right half supported in columns 1..W, find the largest odd time n such that
# column 1 is white at every odd time t <= n (needed if depth 1 is black at all times <= n, since at
# c(t)=0 times consistency forces cell(t,-1) = not cell(t,1)).
import sys
W = int(sys.argv[1]); N = int(sys.argv[2])
best = -1; arg = None
for x0 in range(1 << W):
    x = x0; t = 0; last_ok = -1
    while t < N:
        c = 1 if t % 2 == 0 else 0
        x = ((x << 1) | c) ^ (x | (x >> 1))
        t += 1
        if t % 2 == 1:
            if x & 1:
                break
            last_ok = t
    if last_ok > best:
        best = last_ok; arg = x0
print(f"W={W}: max odd n with column 1 white at all odd t<=n: {best} (start {arg:0{W}b}, horizon {N})")
