# Do two different finite constrained histories ever meet? (G injective on finite constrained configs?)
def step(x): return (x >> 1) ^ (x | (x << 1))
import sys
W = int(sys.argv[1])
images = {}
coll = 0
tot = 0
for x0 in range(1, 1 << W):
    if not (x0 & 1): continue
    x1 = step(x0); x2 = step(x1)
    if not (x2 & 1): continue
    tot += 1
    if x2 in images:
        coll += 1
        if coll <= 5: print("collision:", bin(images[x2]), bin(x0), "->", bin(x2))
    else:
        images[x2] = x0
print("W", W, "constrained 2-steps:", tot, "collisions:", coll)
