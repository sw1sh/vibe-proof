"""Numerical check of the P312 lookback bound (report target 4).

P312 from Wolfram's "Nestedly Recursive Functions" (2024):
    f[n] = 3 + f[n - f[n - 2]],   f[n] = 1 for n <= 0.
The essay says the only values ever needed are f[-3], ..., f[0], and Wolfram's
2024 notebook NestedlyRecursive-05 lists "Get a proof that this only gets to
f[-3]" as a to-do.

Inductive argument (checked numerically below):
    for n >= 20:  (a) 2 f[n] <= n + 20,  (b) n - f[n-2] >= 1,  (c) f[n] >= 7.
    Base cases n <= 19 come from the table; max over all n of 2 f[n] - n is 20, at n = 18.
    Step: (a) at n-2 gives a lookback j = n - f[n-2] >= (n - 18)/2 >= 1, which is (b).
    Since j >= 1 we have f[j] >= 4, so f[n] = 3 + f[j] >= 7, which is (c).
    Finally 2 f[n] = 6 + 2 f[j] <= 6 + j + 20 = n + 26 - f[n-2] <= n + 20,
    because f[n-2] >= 7, which is (a).
Hence the lookback never goes below -3 (reached at n = 4), and it stays >= 1 for n >= 17.
"""
N = 2_000_000
OFF = 10  # f[n] is stored at index n + OFF, so f[-OFF..0] = 1 (padding)

f = [1] * (N + OFF + 1)
for n in range(1, N + 1):
    j = n - f[n - 2 + OFF]
    assert j > -OFF, ("lookback below buffer", n, j)
    f[n + OFF] = 3 + f[j + OFF]
F = lambda n: f[n + OFF]
look = lambda n: n - F(n - 2)

print("f[1..20]:", [F(n) for n in range(1, 21)])
print("min lookback index:", min(look(n) for n in range(1, N + 1)))
print("n reading a seed (index <= 0):", [n for n in range(1, N + 1) if look(n) <= 0])
print("max 2f[n]-n:", max(2 * F(n) - n for n in range(1, N + 1)))
inv = all(2 * F(n) <= n + 20 and look(n) >= 1 and F(n) >= 7 for n in range(20, N + 1))
print("invariant (a),(b),(c) holds for 20 <= n <=", N, ":", inv)
