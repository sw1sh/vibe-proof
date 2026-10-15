# Count rule-30 preimages of the constant configurations on cyclic rings (spatially periodic preimages).
from itertools import product
def F(x):
    n = len(x)
    return tuple(x[(i-1) % n] ^ (x[i] | x[(i+1) % n]) for i in range(n))
for n in range(3, 16):
    z = tuple([0]*n); o = tuple([1]*n)
    c0 = c1 = 0
    for x in product((0,1), repeat=n):
        y = F(x)
        if y == z: c0 += 1
        elif y == o: c1 += 1
    print(n, "preimages of 0^n:", c0, " of 1^n:", c1)
