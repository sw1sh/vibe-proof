# Statistics of L = Phi(f) for uniform random f: densities by depth parity, correlations, zero-run probabilities.
import sys, random
sys.path.insert(0, '.')
from core import *
random.seed(21)
m = 150; N = 3000
Ls = []
for _ in range(N):
    f = [random.getrandbits(1) for _ in range(m)]
    Ls.append(L_of_f(f)[:300])
K = 300
dens_odd = sum(L[k] for L in Ls for k in range(20, K) if (k + 1) % 2 == 1) / (N * len([k for k in range(20, K) if (k + 1) % 2 == 1]))
dens_even = sum(L[k] for L in Ls for k in range(20, K) if (k + 1) % 2 == 0) / (N * len([k for k in range(20, K) if (k + 1) % 2 == 0]))
print('density of ones, odd depths %.4f, even depths %.4f' % (dens_odd, dens_even))
# lag correlations at depth >= 50
for lag in range(1, 9):
    for par in (0, 1):
        num = 0; cnt = 0; s1 = 0; s2 = 0
        for L in Ls:
            for k in range(50 + par, 280, 2):
                num += L[k] * L[k + lag]; s1 += L[k]; s2 += L[k + lag]; cnt += 1
        cov = num / cnt - (s1 / cnt) * (s2 / cnt)
        print('lag %d start parity %d: cov %.4f' % (lag, par, cov), end='; ')
    print()
# zero-run probabilities: P(L zero on [a, a+n)) for a = 101 (odd) and 100 (even)
for a in (100, 101):
    print('a=%d:' % a, ' '.join('n=%d:%.4f(2^-n=%.4f)' % (n, sum(1 for L in Ls if not any(L[a - 1:a - 1 + n])) / N, 2.0 ** -n) for n in range(1, 9)))
