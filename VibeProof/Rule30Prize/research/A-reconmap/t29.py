# Track the stripe front (innermost odd m such that cells m..K follow the stripe) along the slowest orbit.
import sys
sys.path.insert(0, '.')
def step(v, K):
    # v: list cells 1..K-1 ; cell 0 = 0, cell K = 1
    ext = [0] + v + [1]
    return [ext[k + 1] ^ (ext[k] | ext[k - 1]) for k in range(1, K)]
def front(v, K):
    m = K
    while m - 2 >= 1 and v[m - 2 - 1] == 1 and v[m - 1 - 1] == 0: m -= 2
    return m
K = 27
v = [int(c) for c in '00010111110001000101110011']
t = 0; fr = [front(v, K)]
rows = [v]
while front(v, K) > 1:
    v = step(v, K); t += 1; fr.append(front(v, K)); rows.append(v)
print('steps', t)
print('front positions over time:', fr)
for i, r in enumerate(rows[:100]):
    print('%3d %s  front=%d' % (i, ''.join('#' if x else '.' for x in r), fr[i]))
