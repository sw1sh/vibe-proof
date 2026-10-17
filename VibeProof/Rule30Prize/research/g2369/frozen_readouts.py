# Diagonal readouts t -> bit t of g^t(a) for the 8 steps g = f . Phi, f in Aut(T_2)
# (f flips bit 0 by alpha, and bit 1 by beta if bit 0 was 0, by gamma if bit 0 was 1).
import itertools
def Phi(x): return x ^ ((2 * x) | (4 * x))
def make_f(al, be, ga):
    def f(y):
        b0 = y & 1
        return y ^ al ^ (2 * (be if b0 == 0 else ga))
    return f
def eventual_period(seq, maxp=600):
    n = len(seq)
    for p in range(1, maxp + 1):
        # smallest start T with seq[t+p] == seq[t] for all T <= t < n-p
        t = n - p - 1
        while t >= 0 and seq[t + p] == seq[t]:
            t -= 1
        T = t + 1
        if T < n // 2:
            return p, T
    return None
N = 4000
for al, be, ga in itertools.product((0, 1), repeat=3):
    f = make_f(al, be, ga)
    for a in (1, 3, 5):
        x, r = a, []
        for t in range(N):
            r.append((x >> t) & 1)
            x = f(Phi(x))
        ep = eventual_period(r)
        name = {(0,0,0): 'c=Phi', (1,0,0): 'b=sigma.Phi', (1,1,0): 'a=tau.Phi'}.get((al, be, ga), '')
        print(f'f=({al},{be},{ga}) {name:12s} seed {a}: ones={sum(r)/N:.3f}  eventual period:', ep)
