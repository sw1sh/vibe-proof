def step(x): return (x >> 1) ^ (x | (x << 1))
s = "10101011101"   # positions k=1..11 (k=1 next to the wall)
x = 0
for i, ch in enumerate(s):
    if ch == '1': x |= 1 << i
col = []
y = x
for t in range(32):
    col.append(y & 1); y = step(y)
print("column -1:", ''.join(map(str, col)))
print("even times:", [col[t] for t in range(0, 32, 2)])
# forced left half for f_s = col[2s+1], s < 15, then check lam(alt f) on positions 1..30
f = [col[2*s+1] for s in range(15)] + [0]*40
a = []
for s in range(len(f)):
    a += [1, f[s]]
T = len(a)
A = 0
for t, b in enumerate(a):
    if b: A |= 1 << t
prev, cur = 0, A
row = [cur & 1]
for k in range(2, 60):
    T -= 1
    nxt = ((cur >> 1) ^ (cur | prev)) & ((1 << T) - 1)
    prev, cur = cur, nxt
    row.append(cur & 1)
print("lam(alt f) positions 1..40:", ''.join(map(str, row[:40])))
